(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Nameops
open Namegen
open Term
open Termops
open Inductiveops
open Sign
open Environ
open Inductive
open Evd
open Reduction
open Typing
open Pattern
open Matching
open Tacmach
open Proof_type
open Pfedit
open Glob_term
open Evar_refiner
open Tacred
open Tactics
open Tacticals
open Clenv
open Hiddentac
open Libnames
open Nametab
open Smartlocate
open Libobject
open Library
open Printer
open Declarations
open Tacexpr
open Mod_subst

(****************************************************************************)
(*            The Type of Constructions Autotactic Hints                    *)
(****************************************************************************)

type 'a auto_tactic =
  | Res_pf     of constr * 'a (* Hint Apply *)
  | ERes_pf    of constr * 'a (* Hint EApply *)
  | Give_exact of constr
  | Res_pf_THEN_trivial_fail of constr * 'a (* Hint Immediate *)
  | Unfold_nth of evaluable_global_reference       (* Hint Unfold *)
  | Extern     of glob_tactic_expr       (* Hint Extern *)

type 'a gen_auto_tactic = {
  pri  : int;            (* A number lower is higher priority *)
  pat  : constr_pattern option; (* A pattern for the concl of the Goal *)
  name  : global_reference option; (* A potential name to refer to the hint *)
  code : 'a auto_tactic     (* the tactic to apply when the concl matches pat *)
}

type pri_auto_tactic = clausenv gen_auto_tactic

type hint_entry = global_reference option * types gen_auto_tactic

let pri_order_int (id1, {pri=pri1}) (id2, {pri=pri2}) =
  let d = pri1 - pri2 in
    if d == 0 then id2 - id1
    else d

let pri_order t1 t2 = pri_order_int t1 t2 <= 0

let insert v l =
  let rec insrec = function
    | [] -> [v]
    | h::tl -> if pri_order v h then v::h::tl else h::(insrec tl)
  in
  insrec l

(* Nov 98 -- Papageno *)
(* Les Hints sont ré-organisés en plusieurs databases.

  La table impérative "searchtable", de type "hint_db_table",
   associe une database (hint_db) à chaque nom.

  Une hint_db est une table d'association fonctionelle constr -> search_entry
  Le constr correspond à la constante de tête de la conclusion.

  Une search_entry est un triplet comprenant :
     - la liste des tactiques qui n'ont pas de pattern associé
     - la liste des tactiques qui ont un pattern
     - un discrimination net borné (Btermdn.t) constitué de tous les
       patterns de la seconde liste de tactiques *)

type stored_data = int * pri_auto_tactic
    (* First component is the index of insertion in the table, to keep most recent first semantics. *)

let auto_tactic_ord code1 code2 =
  match code1, code2 with
  | Res_pf (c1, _), Res_pf (c2, _)
  | ERes_pf (c1, _), ERes_pf (c2, _)
  | Give_exact c1, Give_exact c2
  | Res_pf_THEN_trivial_fail (c1, _), Res_pf_THEN_trivial_fail (c2, _) -> constr_ord c1 c2
  | Unfold_nth (EvalVarRef i1), Unfold_nth (EvalVarRef i2) -> Pervasives.compare i1 i2
  | Unfold_nth (EvalConstRef c1), Unfold_nth (EvalConstRef c2) ->
      kn_ord (canonical_con c1) (canonical_con c2)
  | Extern t1, Extern t2 -> Pervasives.compare t1 t2
  | _ -> Pervasives.compare code1 code2

module Bounded_net = Btermdn.Make(struct
				    type t = stored_data
				    let compare = pri_order_int
				  end)

type search_entry = stored_data list * stored_data list * Bounded_net.t

let empty_se = ([],[],Bounded_net.create ())

let eq_pri_auto_tactic (_, x) (_, y) =
  if x.pri = y.pri && x.pat = y.pat then
    match x.code,y.code with
      | Res_pf(cstr,_),Res_pf(cstr1,_) -> 
	   eq_constr cstr cstr1
      | ERes_pf(cstr,_),ERes_pf(cstr1,_) -> 
	  eq_constr cstr cstr1
      | Give_exact cstr,Give_exact cstr1  -> 
	  eq_constr cstr cstr1
      | Res_pf_THEN_trivial_fail(cstr,_)
	  ,Res_pf_THEN_trivial_fail(cstr1,_) -> 
	  eq_constr cstr cstr1
      | _,_ -> false
  else
    false

let add_tac pat t st (l,l',dn) =
  match pat with
  | None -> if not (List.exists (eq_pri_auto_tactic t) l) then (insert t l, l', dn) else (l, l', dn)
  | Some pat -> if not (List.exists (eq_pri_auto_tactic t) l') then (l, insert t l', Bounded_net.add st dn (pat,t)) else (l, l', dn)

let rebuild_dn st ((l,l',dn) : search_entry) =
  (l, l', List.fold_left (fun dn (id, t) -> Bounded_net.add (Some st) dn (Option.get t.pat, (id, t)))
    (Bounded_net.create ()) l')


let lookup_tacs (hdc,c) st (l,l',dn) =
  let l'  = List.map snd (Bounded_net.lookup st dn c) in
  let sl' = List.stable_sort pri_order_int l' in
    Sort.merge pri_order l sl'

module Constr_map = Map.Make(RefOrdered)

let is_transparent_gr (ids, csts) = function
  | VarRef id -> Idpred.mem id ids
  | ConstRef cst -> Cpred.mem cst csts
  | IndRef _ | ConstructRef _ -> false

let dummy_goal = Goal.V82.dummy_goal

let translate_hint (go,p) =
  let mk_clenv (c,t) =
    let cl = mk_clenv_from dummy_goal (c,t) in {cl with env = empty_env }
  in
  let code = match p.code with
    | Res_pf (c,t) -> Res_pf (c, mk_clenv (c,t))
    | ERes_pf (c,t) -> ERes_pf (c, mk_clenv (c,t))
    | Res_pf_THEN_trivial_fail (c,t) ->
      Res_pf_THEN_trivial_fail (c, mk_clenv (c,t))
    | Give_exact c -> Give_exact c
    | Unfold_nth e -> Unfold_nth e
    | Extern t -> Extern t
  in
  (go,{ p with code = code })

module Hint_db = struct

  type t = {
    hintdb_state : Names.transparent_state;
    hintdb_unfolds : Idset.t * Cset.t;
    mutable hintdb_max_id : int;
    use_dn : bool;
    hintdb_map : search_entry Constr_map.t;
    (* A list of unindexed entries starting with an unfoldable constant
       or with no associated pattern. *)
    hintdb_nopat : (global_reference option * stored_data) list
  }

  let next_hint_id t = 
    let h = t.hintdb_max_id in t.hintdb_max_id <- succ t.hintdb_max_id; h

  let empty st use_dn = { hintdb_state = st;
			  hintdb_unfolds = (Idset.empty, Cset.empty);
			  hintdb_max_id = 0;
			  use_dn = use_dn;
			  hintdb_map = Constr_map.empty;
			  hintdb_nopat = [] }

  let find key db =
    try Constr_map.find key db.hintdb_map
    with Not_found -> empty_se

  let map_none db =
    List.map snd (Sort.merge pri_order (List.map snd db.hintdb_nopat) [])
    
  let map_all k db =
    let (l,l',_) = find k db in
      List.map snd (Sort.merge pri_order (List.map snd db.hintdb_nopat @ l) l')

  let map_auto (k,c) db =
    let st = if db.use_dn then Some db.hintdb_state else None in
    let l' = lookup_tacs (k,c) st (find k db) in
      List.map snd (Sort.merge pri_order (List.map snd db.hintdb_nopat) l')

  let is_exact = function
    | Give_exact _ -> true
    | _ -> false

  let is_unfold = function
    | Unfold_nth _ -> true
    | _ -> false

  let addkv gr id v db =
    let idv = id, v in
    let k = match gr with
      | Some gr -> if db.use_dn && is_transparent_gr db.hintdb_state gr &&
	  is_unfold v.code then None else Some gr
      | None -> None
    in
    let dnst = if db.use_dn then Some db.hintdb_state else None in
    let pat = if not db.use_dn && is_exact v.code then None else v.pat in
      match k with
      | None ->
	  if not (List.exists (fun (_, (_, v')) -> v = v') db.hintdb_nopat) then
	    { db with hintdb_nopat = (gr,idv) :: db.hintdb_nopat }
	  else db
      | Some gr ->
	  let oval = find gr db in
	    { db with hintdb_map = Constr_map.add gr (add_tac pat idv dnst oval) db.hintdb_map }

  let rebuild_db st' db =
    let db' =
      { db with hintdb_map = Constr_map.map (rebuild_dn st') db.hintdb_map;
	hintdb_state = st'; hintdb_nopat = [] }
    in
      List.fold_left (fun db (gr,(id,v)) -> addkv gr id v db) db' db.hintdb_nopat

  let add_one kv db =
    let (k,v) = translate_hint kv in
    let st',db,rebuild =
      match v.code with
      | Unfold_nth egr ->
	  let addunf (ids,csts) (ids',csts') =
	    match egr with
	    | EvalVarRef id -> (Idpred.add id ids, csts), (Idset.add id ids', csts')
	    | EvalConstRef cst -> (ids, Cpred.add cst csts), (ids', Cset.add cst csts')
	  in 
	  let state, unfs = addunf db.hintdb_state db.hintdb_unfolds in
	    state, { db with hintdb_unfolds = unfs }, true
      | _ -> db.hintdb_state, db, false
    in
    let db = if db.use_dn && rebuild then rebuild_db st' db else db
    in addkv k (next_hint_id db) v db

  let add_list l db = List.fold_right add_one l db

  let remove_sdl p sdl = list_smartfilter p sdl 
  let remove_he st p (sl1, sl2, dn as he) =
    let sl1' = remove_sdl p sl1 and sl2' = remove_sdl p sl2 in
      if sl1' == sl1 && sl2' == sl2 then he
      else rebuild_dn st (sl1', sl2', dn)

  let remove_list grs db =
    let filter (_, h) = match h.name with None -> true | Some gr -> not (List.mem gr grs) in
    let hintmap = Constr_map.map (remove_he db.hintdb_state filter) db.hintdb_map in
    let hintnopat = list_smartfilter (fun (ge, sd) -> filter sd) db.hintdb_nopat in
      { db with hintdb_map = hintmap; hintdb_nopat = hintnopat }

  let remove_one gr db = remove_list [gr] db

  let iter f db =
    f None (List.map snd db.hintdb_nopat);
    Constr_map.iter (fun k (l,l',_) -> f (Some k) (l@l')) db.hintdb_map

  let transparent_state db = db.hintdb_state

  let set_transparent_state db st =
    if db.use_dn then rebuild_db st db
    else { db with hintdb_state = st }

  let unfolds db = db.hintdb_unfolds

  let use_dn db = db.use_dn

end

module Hintdbmap = Gmap

type hint_db = Hint_db.t

type frozen_hint_db_table = (string,hint_db) Hintdbmap.t

type hint_db_table = (string,hint_db) Hintdbmap.t ref

type hint_db_name = string

let searchtable = (ref Hintdbmap.empty : hint_db_table)

let searchtable_map name =
  Hintdbmap.find name !searchtable
let searchtable_add (name,db) =
  searchtable := Hintdbmap.add name db !searchtable
let current_db_names () =
  Hintdbmap.dom !searchtable

(**************************************************************************)
(*                       Definition of the summary                        *)
(**************************************************************************)

let auto_init : (unit -> unit) ref = ref (fun () -> ())
let add_auto_init f = 
  let init = !auto_init in
    auto_init := (fun () -> init (); f ())

let init     () = searchtable := Hintdbmap.empty; !auto_init ()
let freeze   () = !searchtable
let unfreeze fs = searchtable := fs

let _ = Summary.declare_summary "search"
	  { Summary.freeze_function   = freeze;
	    Summary.unfreeze_function = unfreeze;
	    Summary.init_function     = init }


(**************************************************************************)
(*             Auxiliary functions to prepare AUTOHINT objects            *)
(**************************************************************************)

let rec nb_hyp c = match kind_of_term c with
  | Prod(_,_,c2) -> if noccurn 1 c2 then 1+(nb_hyp c2) else nb_hyp c2
  | _ -> 0

(* adding and removing tactics in the search table *)

let try_head_pattern c =
  try head_pattern_bound c
  with BoundPattern -> error "Bound head variable."

let name_of_constr c = try Some (global_of_constr c) with Not_found -> None

let make_exact_entry sigma pri ?name (c,cty) =
  let cty = strip_outer_cast cty in
    match kind_of_term cty with
    | Prod _ -> failwith "make_exact_entry"
    | _ ->
	let pat = snd (Pattern.pattern_of_constr sigma cty) in
	let hd =
	  try head_pattern_bound pat
	  with BoundPattern -> failwith "make_exact_entry"
	in
          (Some hd,
	  { pri = (match pri with None -> 0 | Some p -> p);
	    pat = Some pat;
	    name = name;
	    code = Give_exact c })

let make_apply_entry env sigma (eapply,hnf,verbose) pri ?name (c,cty) =
  let cty = if hnf then hnf_constr env sigma cty else cty in
    match kind_of_term cty with
    | Prod _ ->
        let ce = mk_clenv_from dummy_goal (c,cty) in
	let c' = clenv_type (* ~reduce:false *) ce in
	let pat = snd (Pattern.pattern_of_constr sigma c') in
        let hd =
	  try head_pattern_bound pat
          with BoundPattern -> failwith "make_apply_entry" in
        let nmiss = List.length (clenv_missing ce) in
	if nmiss = 0 then
	  (Some hd,
          { pri = (match pri with None -> nb_hyp cty | Some p -> p);
            pat = Some pat;
	    name = name;
            code = Res_pf(c,cty) })
	else begin
	  if not eapply then failwith "make_apply_entry";
          if verbose then
	    warn (str "the hint: eapply " ++ pr_lconstr c ++
	    str " will only be used by eauto");
          (Some hd,
           { pri = (match pri with None -> nb_hyp cty + nmiss | Some p -> p);
             pat = Some pat;
	     name = name;
             code = ERes_pf(c,cty) })
        end
    | _ -> failwith "make_apply_entry"

(* flags is (e,h,v) with e=true if eapply and h=true if hnf and v=true if verbose
   c is a constr
   cty is the type of constr *)

let make_resolves env sigma flags pri ?name c =
  let cty = Retyping.get_type_of env sigma c in
  let ents =
    map_succeed
      (fun f -> f (c,cty))
      [make_exact_entry sigma pri ?name; make_apply_entry env sigma flags pri ?name]
  in
  if ents = [] then
    errorlabstrm "Hint"
      (pr_lconstr c ++ spc() ++
        (if pi1 flags then str"cannot be used as a hint."
	else str "can be used as a hint only for eauto."));
  ents

(* used to add an hypothesis to the local hint database *)
let make_resolve_hyp env sigma (hname,_,htyp) =
  try
    [make_apply_entry env sigma (true, true, false) None ~name:(VarRef hname)
       (mkVar hname, htyp)]
  with
    | Failure _ -> []
    | e when Logic.catchable_exception e -> anomaly "make_resolve_hyp"

(* REM : in most cases hintname = id *)
let make_unfold eref =
  let g = global_of_evaluable_reference eref in
  (Some g,
   { pri = 4;
     pat = None;
     name = Some g;
     code = Unfold_nth eref })

let make_extern pri pat tacast =
  let hdconstr = Option.map try_head_pattern pat in
  (hdconstr,
   { pri = pri;
     pat = pat;
     name = None;
     code = Extern tacast })

let make_trivial env sigma ?name c =
  let t = hnf_constr env sigma (type_of env sigma c) in
  let hd = head_of_constr_reference (fst (head_constr t)) in
  let ce = mk_clenv_from dummy_goal (c,t) in
  (Some hd, { pri=1;
              pat = Some (snd (Pattern.pattern_of_constr sigma (clenv_type ce)));
	      name = name;
              code=Res_pf_THEN_trivial_fail(c,t) })
  
open Vernacexpr

(**************************************************************************)
(*               declaration of the AUTOHINT library object               *)
(**************************************************************************)

(* If the database does not exist, it is created *)
(* TODO: should a warning be printed in this case ?? *)

let get_db dbname =
  try searchtable_map dbname
  with Not_found -> Hint_db.empty empty_transparent_state false

let add_hint dbname hintlist = 
  let db = get_db dbname in
  let db' = Hint_db.add_list hintlist db in
    searchtable_add (dbname,db')

let add_transparency dbname grs b =
  let db = get_db dbname in
  let st = Hint_db.transparent_state db in
  let st' =
    List.fold_left (fun (ids, csts) gr ->
      match gr with
      | EvalConstRef c -> (ids, (if b then Cpred.add else Cpred.remove) c csts)
      | EvalVarRef v -> (if b then Idpred.add else Idpred.remove) v ids, csts)
      st grs
  in searchtable_add (dbname, Hint_db.set_transparent_state db st')

let remove_hints dbname hintlist grs =
  let db = get_db dbname in
  let db' = Hint_db.remove_list grs db in
    searchtable_add (dbname, db')

type hint_action =
  | CreateDB of bool * transparent_state
  | AddTransparency of evaluable_global_reference list * bool
  | AddHints of hint_entry list
  | RemoveHints of global_reference list

type hint_obj = bool * string * hint_action  (* locality, name, action *)

let cache_autohint (_,(local,name,hints)) =
  match hints with
  | CreateDB (b, st) -> searchtable_add (name, Hint_db.empty st b)
  | AddTransparency (grs, b) -> add_transparency name grs b
  | AddHints hints -> add_hint name hints
  | RemoveHints grs -> remove_hints name hints grs

let forward_subst_tactic =
  ref (fun _ -> failwith "subst_tactic is not installed for auto")

let set_extern_subst_tactic f = forward_subst_tactic := f

let subst_autohint (subst,(local,name,hintlist as obj)) =
  let subst_key gr =
    let (lab'', elab') = subst_global subst gr in
    let gr' =
      (try head_of_constr_reference (fst (head_constr_bound elab'))
       with Tactics.Bound -> lab'')
    in if gr' == gr then gr else gr'
  in
  let subst_hint (k,data as hint) =
    let k' = Option.smartmap subst_key k in
    let pat' = Option.smartmap (subst_pattern subst) data.pat in
    let code' = match data.code with
      | Res_pf (c,t) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t'==t then data.code else Res_pf (c', t')
      | ERes_pf (c,t) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t'==t then data.code else ERes_pf (c',t')
      | Give_exact c ->
          let c' = subst_mps subst c in
          if c==c' then data.code else Give_exact c'
      | Res_pf_THEN_trivial_fail (c,t) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t==t' then data.code else Res_pf_THEN_trivial_fail (c',t')
      | Unfold_nth ref ->
          let ref' = subst_evaluable_reference subst ref in
          if ref==ref' then data.code else Unfold_nth ref'
      | Extern tac ->
	  let tac' = !forward_subst_tactic subst tac in
	  if tac==tac' then data.code else Extern tac'
    in
    let data' =
      if data.pat==pat' && data.code==code' then data
      else { data with pat = pat'; code = code' }
    in
    if k' == k && data' == data then hint else (k',data')
  in
    match hintlist with
    | CreateDB _ -> obj
    | AddTransparency (grs, b) ->
	let grs' = list_smartmap (subst_evaluable_reference subst) grs in
	  if grs==grs' then obj else (local, name, AddTransparency (grs', b))
    | AddHints hintlist ->
	let hintlist' = list_smartmap subst_hint hintlist in
	  if hintlist' == hintlist then obj else
	    (local,name,AddHints hintlist')
    | RemoveHints grs ->
	let grs' = list_smartmap (fun x -> fst (subst_global subst x)) grs in
	  if grs==grs' then obj else (local, name, RemoveHints grs')


let classify_autohint ((local,name,hintlist) as obj) =
  if local or hintlist = (AddHints []) then Dispose else Substitute obj

let inAutoHint : hint_obj -> obj =
  declare_object {(default_object "AUTOHINT") with
                    cache_function = cache_autohint;
		    load_function = (fun _ -> cache_autohint);
		    subst_function = subst_autohint;
		    classify_function = classify_autohint }


let create_hint_db l n st b =
  Lib.add_anonymous_leaf (inAutoHint (l,n,CreateDB (b, st)))

let remove_hints local dbnames grs =
  let dbnames = if dbnames = [] then ["core"] else dbnames in
    List.iter
      (fun dbname ->
	 Lib.add_anonymous_leaf (inAutoHint(local, dbname, RemoveHints grs)))
      dbnames

(**************************************************************************)
(*                     The "Hint" vernacular command                      *)
(**************************************************************************)
let add_resolves env sigma clist local dbnames =
  List.iter
    (fun dbname ->
       Lib.add_anonymous_leaf
	 (inAutoHint
	    (local,dbname, AddHints
     	      (List.flatten (List.map (fun (x, hnf, name, y) ->
		make_resolves env sigma (true,hnf,Flags.is_verbose()) x ?name y) clist)))))
    dbnames


let add_unfolds l local dbnames =
  List.iter
    (fun dbname -> Lib.add_anonymous_leaf
       (inAutoHint (local,dbname, AddHints (List.map make_unfold l))))
    dbnames

let add_transparency l b local dbnames =
  List.iter
    (fun dbname -> Lib.add_anonymous_leaf
       (inAutoHint (local,dbname, AddTransparency (l, b))))
    dbnames

let add_extern pri pat tacast local dbname =
  (* We check that all metas that appear in tacast have at least
     one occurence in the left pattern pat *)
  let tacmetas = [] in
    match pat with
    | Some (patmetas,pat) ->
	(match (list_subtract tacmetas patmetas) with
	| i::_ ->
	    errorlabstrm "add_extern"
	      (str "The meta-variable ?" ++ Ppconstr.pr_patvar i ++ str" is not bound.")
	| []  ->
	    Lib.add_anonymous_leaf
	      (inAutoHint(local,dbname, AddHints [make_extern pri (Some pat) tacast])))
    | None ->
	Lib.add_anonymous_leaf
	  (inAutoHint(local,dbname, AddHints [make_extern pri None tacast]))

let add_externs pri pat tacast local dbnames =
  List.iter (add_extern pri pat tacast local) dbnames

let add_trivials env sigma l local dbnames =
  List.iter
    (fun dbname ->
       Lib.add_anonymous_leaf (
	 inAutoHint(local,dbname, AddHints (List.map (fun (name, c) -> make_trivial env sigma ?name c) l))))
    dbnames

let forward_intern_tac =
  ref (fun _ -> failwith "intern_tac is not installed for auto")

let set_extern_intern_tac f = forward_intern_tac := f

type hints_entry =
  | HintsResolveEntry of (int option * bool * global_reference option * constr) list
  | HintsImmediateEntry of (global_reference option * constr) list
  | HintsUnfoldEntry of evaluable_global_reference list
  | HintsTransparencyEntry of evaluable_global_reference list * bool
  | HintsExternEntry of
      int * (patvar list * constr_pattern) option * glob_tactic_expr
  | HintsDestructEntry of identifier * int * (bool,unit) location *
      (patvar list * constr_pattern) * glob_tactic_expr

let h = id_of_string "H"

exception Found of constr * types

let prepare_hint env (sigma,c) =
  let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
  (* We re-abstract over uninstantiated evars.
     It is actually a bit stupid to generalize over evars since the first
     thing make_resolves will do is to re-instantiate the products *)
  let c = drop_extra_implicit_args (Evarutil.nf_evar sigma c) in
  let vars = ref (collect_vars c) in
  let subst = ref [] in
  let rec find_next_evar c = match kind_of_term c with
    | Evar (evk,args as ev) ->
      (* We skip the test whether args is the identity or not *)
      let t = Evarutil.nf_evar sigma (existential_type sigma ev) in
      let t = List.fold_right (fun (e,id) c -> replace_term e id c) !subst t in
      if free_rels t <> Intset.empty then
	error "Hints with holes dependent on a bound variable not supported.";
      if occur_existential t then
	(* Not clever enough to construct dependency graph of evars *)
	error "Not clever enough to deal with evars dependent in other evars.";
      raise (Found (c,t))
    | _ -> iter_constr find_next_evar c in
  let rec iter c =
    try find_next_evar c; c
    with Found (evar,t) ->
      let id = next_ident_away_from h (fun id -> Idset.mem id !vars) in
      vars := Idset.add id !vars;
      subst := (evar,mkVar id)::!subst;
      mkNamedLambda id t (iter (replace_term evar (mkVar id) c)) in
  iter c

let name_of_constr_expr c =
  match c with
  | Topconstr.CRef r -> (try Some (global r) with _ -> None)
  | _ -> None 
      
let interp_hints h =
  let f c =
    let evd,c = Constrintern.interp_open_constr Evd.empty (Global.env()) c in
    let c = prepare_hint (Global.env()) (evd,c) in
    Evarutil.check_evars (Global.env()) Evd.empty evd c;
    c in
  let fr r =
    let gr = global_with_alias r in
    let r' = evaluable_of_global_reference (Global.env()) gr in
    Dumpglob.add_glob (loc_of_reference r) gr;
    r' in
  let fres (o, b, c) = (o, b, name_of_constr_expr c, f c) in
  let fi c = name_of_constr_expr c, f c in
  let fp = Constrintern.intern_constr_pattern Evd.empty (Global.env()) in
  match h with
  | HintsResolve lhints -> HintsResolveEntry (List.map fres lhints)
  | HintsImmediate lhints -> HintsImmediateEntry (List.map fi lhints)
  | HintsUnfold lhints -> HintsUnfoldEntry (List.map fr lhints)
  | HintsTransparency (lhints, b) ->
      HintsTransparencyEntry (List.map fr lhints, b)
  | HintsConstructors lqid ->
      let constr_hints_of_ind qid =
        let ind = global_inductive_with_alias qid in
        list_tabulate (fun i -> let c = (ind,i+1) in
			 None, true, Some (ConstructRef c), mkConstruct c)
	  (nconstructors ind) in
	HintsResolveEntry (List.flatten (List.map constr_hints_of_ind lqid))
  | HintsExtern (pri, patcom, tacexp) ->
      let pat =	Option.map fp patcom in
      let tacexp = !forward_intern_tac (match pat with None -> [] | Some (l, _) -> l) tacexp in
      HintsExternEntry (pri, pat, tacexp)
  | HintsDestruct(na,pri,loc,pat,code) ->
      let (l,_ as pat) = fp pat in
      HintsDestructEntry (na,pri,loc,pat,!forward_intern_tac l code)

let add_hints local dbnames0 h =
  if List.mem "nocore" dbnames0 then
    error "The hint database \"nocore\" is meant to stay empty.";
  let dbnames = if dbnames0 = [] then ["core"] else dbnames0 in
  let env = Global.env() and sigma = Evd.empty in
  match h with
  | HintsResolveEntry lhints -> add_resolves env sigma lhints local dbnames
  | HintsImmediateEntry lhints -> add_trivials env sigma lhints local dbnames
  | HintsUnfoldEntry lhints -> add_unfolds lhints local dbnames
  | HintsTransparencyEntry (lhints, b) ->
      add_transparency lhints b local dbnames
  | HintsExternEntry (pri, pat, tacexp) ->
      add_externs pri pat tacexp local dbnames
  | HintsDestructEntry (na,pri,loc,pat,code) ->
      if dbnames0<>[] then
        warn (str"Database selection not implemented for destruct hints");
      Dhyp.add_destructor_hint local na loc pat pri code

(**************************************************************************)
(*                    Functions for printing the hints                    *)
(**************************************************************************)

let pr_autotactic =
  function
  | Res_pf (c,clenv) -> (str"apply " ++ pr_lconstr c)
  | ERes_pf (c,clenv) -> (str"eapply " ++ pr_lconstr c)
  | Give_exact c -> (str"exact " ++ pr_lconstr c)
  | Res_pf_THEN_trivial_fail (c,clenv) ->
      (str"apply " ++ pr_lconstr c ++ str" ; trivial")
  | Unfold_nth c -> (str"unfold " ++  pr_evaluable_reference c)
  | Extern tac ->
      (str "(external) " ++ Pptactic.pr_glob_tactic (Global.env()) tac)

let pr_hint (id, v) =
  (pr_autotactic v.code ++ str"(level " ++ int v.pri ++ str", id " ++ int id ++ str ")" ++ spc ())

let pr_hint_list hintlist =
  (str "  " ++ hov 0 (prlist pr_hint hintlist) ++ fnl ())

let pr_hints_db (name,db,hintlist) =
  (str "In the database " ++ str name ++ str ":" ++
     if hintlist = [] then (str " nothing" ++ fnl ())
     else (fnl () ++ pr_hint_list hintlist))

(* Print all hints associated to head c in any database *)
let pr_hint_list_for_head c =
  let dbs = Hintdbmap.to_list !searchtable in
  let valid_dbs =
    map_succeed
      (fun (name,db) -> (name,db, List.map (fun v -> 0, v) (Hint_db.map_all c db)))
      dbs
  in
  if valid_dbs = [] then
    (str "No hint declared for :" ++ pr_global c)
  else
    hov 0
      (str"For " ++ pr_global c ++ str" -> " ++ fnl () ++
	 hov 0 (prlist pr_hints_db valid_dbs))

let pr_hint_ref ref = pr_hint_list_for_head ref

(* Print all hints associated to head id in any database *)
let print_hint_ref ref =  ppnl(pr_hint_ref ref)

let pr_hint_term cl =
  try
    let dbs = Hintdbmap.to_list !searchtable in
    let valid_dbs =
      let fn = try
	  let (hdc,args) = head_constr_bound cl in
	  let hd = head_of_constr_reference hdc in
	    if occur_existential cl then
	      Hint_db.map_all hd
	    else Hint_db.map_auto (hd, applist (hdc,args))
	with Bound -> Hint_db.map_none
      in
      let fn db = List.map (fun x -> 0, x) (fn db) in
	map_succeed (fun (name, db) -> (name, db, fn db)) dbs
    in
      if valid_dbs = [] then
	(str "No hint applicable for current goal")
      else
	(str "Applicable Hints :" ++ fnl () ++
	    hov 0 (prlist pr_hints_db valid_dbs))
  with Match_failure _ | Failure _ ->
    (str "No hint applicable for current goal")

let error_no_such_hint_database x =
  error ("No such Hint database: "^x^".")

let print_hint_term cl = ppnl (pr_hint_term cl)

(* print all hints that apply to the concl of the current goal *)
let print_applicable_hint () =
  let pts = get_pftreestate () in
  let glss = Proof.V82.subgoals pts in
  match glss.Evd.it with
  | [] -> Util.error "No focused goal."
  | g::_ ->
    let gl = { Evd.it = g; sigma = glss.Evd.sigma } in
    print_hint_term (pf_concl gl)

(* displays the whole hint database db *)
let print_hint_db db =
  let (ids, csts) = Hint_db.transparent_state db in
  msgnl (hov 0
	  ((if Hint_db.use_dn db then str"Discriminated database"
	    else str"Non-discriminated database")));
  msgnl (hov 2 (str"Unfoldable variable definitions: " ++ pr_idpred ids));
  msgnl (hov 2 (str"Unfoldable constant definitions: " ++ pr_cpred csts));
  Hint_db.iter
    (fun head hintlist ->
      match head with
      | Some head ->
	  msg (hov 0
		  (str "For " ++ pr_global head ++ str " -> " ++
		      pr_hint_list hintlist))
      | None ->
	  msg (hov 0
		  (str "For any goal -> " ++
		      pr_hint_list hintlist)))
    db

let print_hint_db_by_name dbname =
  try
    let db = searchtable_map dbname in print_hint_db db
  with Not_found ->
    error_no_such_hint_database dbname

(* displays all the hints of all databases *)
let print_searchtable () =
  Hintdbmap.iter
    (fun name db ->
       msg (str "In the database " ++ str name ++ str ":" ++ fnl ());
       print_hint_db db)
    !searchtable

(**************************************************************************)
(*                           Automatic tactics                            *)
(**************************************************************************)

(**************************************************************************)
(*          tactics with a trace mechanism for automatic search           *)
(**************************************************************************)

let priority l = List.filter (fun (_, hint) -> hint.pri = 0) l

(* tell auto not to reuse already instantiated metas in unification (for
   compatibility, since otherwise, apply succeeds oftener) *)

open Unification

let auto_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = empty_transparent_state;
  modulo_delta_types = full_transparent_state;
  resolve_evars = true;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true;
  frozen_evars = ExistentialSet.empty;
  restrict_conv_on_strict_subterms = false; (* Compat *)
  modulo_betaiota = false;
  modulo_eta = true;
  allow_K_in_toplevel_higher_order_unification = false
}

(* Try unification with the precompiled clause, then use registered Apply *)

let h_clenv_refine ev c clenv =
  Refiner.abstract_tactic (TacApply (true,ev,[c,NoBindings],None))
    (Clenvtac.clenv_refine ev clenv)

let unify_resolve_nodelta (c,clenv) gl =
  let clenv' = connect_clenv gl clenv in
  let clenv'' = clenv_unique_resolver ~flags:auto_unif_flags clenv' gl in
  h_clenv_refine false c clenv'' gl

let unify_resolve flags (c,clenv) gl =
  let clenv' = connect_clenv gl clenv in
  let clenv'' = clenv_unique_resolver ~flags clenv' gl in
  h_clenv_refine false c clenv'' gl

let unify_resolve_gen = function
  | None -> unify_resolve_nodelta
  | Some flags -> unify_resolve flags

(* Util *)

let expand_constructor_hints env lems =
  list_map_append (fun (sigma,lem) ->
    match kind_of_term lem with
    | Ind ind ->
	list_tabulate (fun i -> mkConstruct (ind,i+1)) (nconstructors ind)
    | _ ->
	[prepare_hint env (sigma,lem)]) lems

(* builds a hint database from a constr signature *)
(* typically used with (lid, ltyp) = pf_hyps_types <some goal> *)

let add_hint_lemmas eapply lems hint_db gl =
  let lems = expand_constructor_hints (pf_env gl) lems in
  let hintlist' =
    list_map_append (pf_apply make_resolves gl (eapply,true,false) None) lems in
  Hint_db.add_list hintlist' hint_db

let make_local_hint_db ?ts eapply lems gl =
  let sign = pf_hyps gl in
  let ts = match ts with
    | None -> Hint_db.transparent_state (searchtable_map "core") 
    | Some ts -> ts
  in
  let hintlist = list_map_append (pf_apply make_resolve_hyp gl) sign in
  add_hint_lemmas eapply lems
    (Hint_db.add_list hintlist (Hint_db.empty ts false)) gl

(* Serait-ce possible de compiler d'abord la tactique puis de faire la
   substitution sans passer par bdize dont l'objectif est de préparer un
   terme pour l'affichage ? (HH) *)

(* Si on enlève le dernier argument (gl) conclPattern est calculé une
fois pour toutes : en particulier si Pattern.somatch produit une UserError
Ce qui fait que si la conclusion ne matche pas le pattern, Auto échoue, même
si après Intros la conclusion matche le pattern.
*)

(* conclPattern doit échouer avec error car il est rattraper par tclFIRST *)

let forward_interp_tactic =
  ref (fun _ -> failwith "interp_tactic is not installed for auto")

let set_extern_interp f = forward_interp_tactic := f

let conclPattern concl pat tac gl =
  let constr_bindings =
    match pat with
    | None -> []
    | Some pat ->
	try matches pat concl
	with PatternMatchingFailure -> error "conclPattern" in
    !forward_interp_tactic constr_bindings tac gl

(**************************************************************************)
(*                           The Trivial tactic                           *)
(**************************************************************************)

(* local_db is a Hint database containing the hypotheses of current goal *)
(* Papageno : cette fonction a été pas mal simplifiée depuis que la base
  de Hint impérative a été remplacée par plusieurs bases fonctionnelles *)

let flags_of_state st =
  {auto_unif_flags with
    modulo_conv_on_closed_terms = Some st; modulo_delta = st}

let hintmap_of hdc concl =
  match hdc with
  | None -> Hint_db.map_none
  | Some hdc ->
      if occur_existential concl then Hint_db.map_all hdc
      else Hint_db.map_auto (hdc,concl)

let exists_evaluable_reference env = function
  | EvalConstRef _ -> true
  | EvalVarRef v -> try ignore(lookup_named v env); true with Not_found -> false

let rec trivial_fail_db mod_delta db_list local_db gl =
  let intro_tac =
    tclTHEN intro
      (fun g'->
	 let hintl = make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
	 in trivial_fail_db mod_delta db_list (Hint_db.add_list hintl local_db) g')
  in
  tclFIRST
    (assumption::intro_tac::
     (List.map (fun tac -> tclCOMPLETE tac)
       (trivial_resolve mod_delta db_list local_db (pf_concl gl)))) gl

and my_find_search_nodelta db_list local_db hdc concl =
  List.map (fun hint -> (None,hint))
    (list_map_append (hintmap_of hdc concl) (local_db::db_list))

and my_find_search mod_delta =
  if mod_delta then my_find_search_delta
  else my_find_search_nodelta

and my_find_search_delta db_list local_db hdc concl =
  let flags = {auto_unif_flags with use_metas_eagerly_in_conv_on_closed_terms = true} in
  let f = hintmap_of hdc concl in
    if occur_existential concl then
      list_map_append
	(fun db ->
	  if Hint_db.use_dn db then
	    let flags = flags_of_state (Hint_db.transparent_state db) in
	      List.map (fun x -> (Some flags,x)) (f db)
	  else
	    let flags = {flags with modulo_delta = Hint_db.transparent_state db} in
	      List.map (fun x -> (Some flags,x)) (f db))
	(local_db::db_list)
    else
      list_map_append (fun db ->
	if Hint_db.use_dn db then
	  let flags = flags_of_state (Hint_db.transparent_state db) in
	    List.map (fun x -> (Some flags, x)) (f db)
	else
	  let (ids, csts as st) = Hint_db.transparent_state db in
	  let flags, l =
	    let l =
	      match hdc with None -> Hint_db.map_none db
	      | Some hdc ->
		  if (Idpred.is_empty ids && Cpred.is_empty csts)
		  then Hint_db.map_auto (hdc,concl) db
		  else Hint_db.map_all hdc db
	    in {flags with modulo_delta = st}, l
	  in List.map (fun x -> (Some flags,x)) l)
      	(local_db::db_list)

and tac_of_hint db_list local_db concl (flags, ({pat=p; code=t})) =
  let tactic = 
    match t with
    | Res_pf (c,cl) -> unify_resolve_gen flags (c,cl)
    | ERes_pf _ -> (fun gl -> error "eres_pf")
    | Give_exact c  -> exact_check c
    | Res_pf_THEN_trivial_fail (c,cl) ->
      tclTHEN
        (unify_resolve_gen flags (c,cl))
        (trivial_fail_db (flags <> None) db_list local_db)
    | Unfold_nth c -> 
      (fun gl ->
       if exists_evaluable_reference (pf_env gl) c then
	 tclPROGRESS (h_reduce (Unfold [all_occurrences_expr,c]) onConcl) gl
       else tclFAIL 0 (str"Unbound reference") gl)
    | Extern tacast -> conclPattern concl p tacast
  in tactic

and trivial_resolve mod_delta db_list local_db cl =
  try
    let head =
      try let hdconstr,_ = head_constr_bound cl in
	    Some (head_of_constr_reference hdconstr)
      with Bound -> None
    in
      List.map (tac_of_hint db_list local_db cl)
	(priority
	    (my_find_search mod_delta db_list local_db head cl))
  with Not_found -> []

(** Two ways to disable the use of the "core" database:
    - Via the optional argument : use_core_db=false
      This is kept for compatibility with the rippling plugin.
    - By passing "nocore" amongst the databases *)

let make_db_list ?(use_core_db=true) dbnames =
  let use_core = use_core_db && not (List.mem "nocore" dbnames) in
  let dbnames = list_remove "nocore" dbnames in
  let dbnames = if use_core then "core"::dbnames else dbnames in
  let lookup db =
    try searchtable_map db with Not_found -> error_no_such_hint_database db
  in
  List.map lookup dbnames

let trivial lems dbnames gl =
  let db_list = make_db_list dbnames in
  tclTRY (trivial_fail_db false db_list (make_local_hint_db false lems gl)) gl

let full_trivial lems gl =
  let dbnames = Hintdbmap.dom !searchtable in
  let dbnames = list_remove "v62" dbnames in
  let db_list = List.map (fun x -> searchtable_map x) dbnames in
  tclTRY (trivial_fail_db false db_list (make_local_hint_db false lems gl)) gl

let gen_trivial lems = function
  | None -> full_trivial lems
  | Some l -> trivial lems l

let h_trivial lems l =
  Refiner.abstract_tactic (TacTrivial (List.map snd lems,l))
    (gen_trivial lems l)

(**************************************************************************)
(*                       The classical Auto tactic                        *)
(**************************************************************************)

let possible_resolve mod_delta db_list local_db cl =
  try
    let head =
      try let hdconstr,_ = head_constr_bound cl in
	    Some (head_of_constr_reference hdconstr)
      with Bound -> None
    in
      List.map (tac_of_hint db_list local_db cl)
	(my_find_search mod_delta db_list local_db head cl)
  with Not_found -> []

let decomp_unary_term_then (id,_,typc) kont1 kont2 gl =
  try
    let ccl = applist (head_constr typc) in
    match Hipattern.match_with_conjunction ccl with
    | Some (_,args) ->
	tclTHEN (simplest_case (mkVar id)) (kont1 (List.length args)) gl
    | None ->
	kont2 gl
  with UserError _ -> kont2 gl

let decomp_empty_term (id,_,typc) gl =
  if Hipattern.is_empty_type typc then
    simplest_case (mkVar id) gl
  else
    errorlabstrm "Auto.decomp_empty_term" (str "Not an empty type.")

let extend_local_db gl decl db =
  Hint_db.add_list (make_resolve_hyp (pf_env gl) (project gl) decl) db

(* Try to decompose hypothesis [decl] into atomic components of a
   conjunction with maximum depth [p] (or solve the goal from an
   empty type) then call the continuation tactic with hint db extended
   with the obtained not-further-decomposable hypotheses *)

let rec decomp_and_register_decl p kont (id,_,_ as decl) db gl =
  if p = 0 then
    kont (extend_local_db gl decl db) gl
  else
    tclORELSE0
      (decomp_empty_term decl)
      (decomp_unary_term_then decl (intros_decomp (p-1) kont [] db)
	(kont (extend_local_db gl decl db))) gl

(* Introduce [n] hypotheses, then decompose then with maximum depth [p] and
   call the continuation tactic [kont] with the hint db extended
   with the so-obtained not-further-decomposable hypotheses *)

and intros_decomp p kont decls db n =
  if n = 0 then
    decomp_and_register_decls p kont decls db
  else
    tclTHEN intro (onLastDecl (fun d ->
      (intros_decomp p kont (d::decls) db (n-1))))

(* Decompose hypotheses [hyps] with maximum depth [p] and
   call the continuation tactic [kont] with the hint db extended
   with the so-obtained not-further-decomposable hypotheses *)

and decomp_and_register_decls p kont decls =
  List.fold_left (decomp_and_register_decl p) kont decls


(* decomp is an natural number giving an indication on decomposition
   of conjunction in hypotheses, 0 corresponds to no decomposition *)
(* n is the max depth of search *)
(* local_db contains the local Hypotheses *)

exception Uplift of tactic list

let search_gen p n mod_delta db_list local_db =
  let rec search n local_db =
    if n=0 then (fun gl -> error "BOUND 2") else
      tclORELSE0 assumption
	(tclORELSE0 (intros_decomp p (search n) [] local_db 1)
	   (fun gl -> tclFIRST
	      (List.map (fun ntac -> tclTHEN ntac (search (n-1) local_db))
		 (possible_resolve mod_delta db_list local_db (pf_concl gl))) gl))
  in
  search n local_db

let search = search_gen 0

let default_search_depth = ref 5

let delta_auto ?(use_core_db=true) mod_delta n lems dbnames gl =
  let db_list = make_db_list ~use_core_db dbnames in
  tclTRY (search n mod_delta db_list (make_local_hint_db false lems gl)) gl

let auto ?(use_core_db=true) = delta_auto ~use_core_db false

let new_auto ?(use_core_db=true) = delta_auto ~use_core_db true

let default_auto = auto !default_search_depth [] []

let delta_full_auto mod_delta n lems gl =
  let dbnames = Hintdbmap.dom !searchtable in
  let dbnames = list_remove "v62" dbnames in
  let db_list = List.map (fun x -> searchtable_map x) dbnames in
  tclTRY (search n mod_delta db_list (make_local_hint_db false lems gl)) gl

let full_auto = delta_full_auto false
let new_full_auto = delta_full_auto true

let default_full_auto gl = full_auto !default_search_depth [] gl

let gen_auto n lems dbnames =
  let n = match n with None -> !default_search_depth | Some n -> n in
  match dbnames with
  | None -> full_auto n lems
  | Some l -> auto n lems l

let inj_or_var = Option.map (fun n -> ArgArg n)

let h_auto n lems l =
  Refiner.abstract_tactic (TacAuto (inj_or_var n,List.map snd lems,l))
    (gen_auto n lems l)

(**************************************************************************)
(*                  The "destructing Auto" from Eduardo                   *)
(**************************************************************************)

(* Depth of search after decomposition of hypothesis, by default
   one look for an immediate solution *)
let default_search_decomp = ref 20

let destruct_auto p lems n gl =
  decomp_and_register_decls p (fun local_db gl ->
    search_gen p n false (List.map searchtable_map ["core";"extcore"])
      (add_hint_lemmas false lems local_db gl) gl)
    (pf_hyps gl)
    (Hint_db.empty empty_transparent_state false)
    gl

let dautomatic des_opt lems n = tclTRY (destruct_auto des_opt lems n)

let dauto (n,p) lems =
  let p = match p with Some p -> p | None -> !default_search_decomp in
  let n = match n with Some n -> n | None -> !default_search_depth in
  dautomatic p lems n

let default_dauto = dauto (None,None) []

let h_dauto (n,p) lems =
  Refiner.abstract_tactic (TacDAuto (inj_or_var n,p,List.map snd lems))
    (dauto (n,p) lems)

(***************************************)
(*** A new formulation of Auto *********)
(***************************************)

let make_resolve_any_hyp env sigma (id,_,ty) =
  let ents =
    map_succeed
      (fun f -> f (mkVar id,ty))
      [make_exact_entry sigma None; make_apply_entry env sigma (true,true,false) None]
  in
  ents

type autoArguments =
  | UsingTDB
  | Destructing

let compileAutoArg contac = function
  | Destructing ->
      (function g ->
         let ctx = pf_hyps g in
	 tclFIRST
           (List.map
              (fun (id,_,typ) ->
                let cl = (strip_prod_assum typ) in
                 if Hipattern.is_conjunction cl
		 then
		   tclTHENSEQ [simplest_elim (mkVar id); clear [id]; contac]
                 else
		   tclFAIL 0 (pr_id id ++ str" is not a conjunction"))
	     ctx) g)
  | UsingTDB ->
      (tclTHEN
         (Tacticals.tryAllHypsAndConcl
            (function
               | Some id -> Dhyp.h_destructHyp false id
               | None    -> Dhyp.h_destructConcl))
         contac)

let compileAutoArgList contac = List.map (compileAutoArg contac)

let rec super_search n db_list local_db argl gl =
  if n = 0 then error "BOUND 2";
  tclFIRST
    (assumption
     ::
     tclTHEN intro
        (fun g ->
	   let hintl = pf_apply make_resolve_any_hyp g (pf_last_hyp g) in
	   super_search n db_list (Hint_db.add_list hintl local_db)
	     argl g)
     ::
     List.map (fun ntac ->
            tclTHEN ntac
              (super_search (n-1) db_list local_db argl))
         (possible_resolve false db_list local_db (pf_concl gl))
      @
      compileAutoArgList (super_search (n-1) db_list local_db argl) argl) gl

let search_superauto n to_add argl g =
  let sigma =
    List.fold_right
      (fun (id,c) -> add_named_decl (id, None, pf_type_of g c))
      to_add empty_named_context in
  let db0 = list_map_append (make_resolve_hyp (pf_env g) (project g)) sigma in
  let db = Hint_db.add_list db0 (make_local_hint_db false [] g) in
  super_search n [Hintdbmap.find "core" !searchtable] db argl g

let superauto n to_add argl  =
  tclTRY (tclCOMPLETE (search_superauto n to_add argl))

let interp_to_add gl r =
  let r = locate_global_with_alias (qualid_of_reference r) in
  let id = basename_of_global r in
  (next_ident_away id (pf_ids_of_hyps gl), constr_of_global r)

let gen_superauto nopt l a b gl =
  let n = match nopt with Some n -> n | None -> !default_search_depth in
  let al = (if a then [Destructing] else [])@(if b then [UsingTDB] else []) in
  superauto n (List.map (interp_to_add gl) l) al gl

let h_superauto no l a b =
  Refiner.abstract_tactic (TacSuperAuto (no,l,a,b)) (gen_superauto no l a b)

