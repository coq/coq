(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Errors
open Names
open Vars
open Term
open Environ
open Mod_subst
open Globnames
open Libobject
open Namegen
open Libnames
open Smartlocate
open Misctypes
open Evd
open Termops
open Inductiveops
open Typing
open Tacexpr
open Decl_kinds
open Pattern
open Patternops
open Clenv
open Pfedit
open Tacred
open Printer
open Vernacexpr

(****************************************)
(* General functions                    *)
(****************************************)

exception Bound

let head_constr_bound t =
  let t = strip_outer_cast t in
  let _,ccl = decompose_prod_assum t in
  let hd,args = decompose_app ccl in
  match kind_of_term hd with
    | Const _ | Ind _ | Construct _ | Var _ -> hd
    | Proj (p, _) -> mkConst (Projection.constant p)
    | _ -> raise Bound

let head_constr c =
  try head_constr_bound c with Bound -> error "Bound head variable."

let decompose_app_bound t =
  let t = strip_outer_cast t in
  let _,ccl = decompose_prod_assum t in
  let hd,args = decompose_app_vect ccl in
  match kind_of_term hd with
    | Const (c,u) -> ConstRef c, args
    | Ind (i,u) -> IndRef i, args
    | Construct (c,u) -> ConstructRef c, args
    | Var id -> VarRef id, args
    | Proj (p, c) -> ConstRef (Projection.constant p), Array.cons c args
    | _ -> raise Bound

(************************************************************************)
(*           The Type of Constructions Autotactic Hints                 *)
(************************************************************************)

type 'a auto_tactic =
  | Res_pf     of 'a (* Hint Apply *)
  | ERes_pf    of 'a (* Hint EApply *)
  | Give_exact of 'a
  | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
  | Unfold_nth of evaluable_global_reference       (* Hint Unfold *)
  | Extern     of glob_tactic_expr       (* Hint Extern *)

type hints_path_atom = 
  | PathHints of global_reference list
  | PathAny

type hints_path =
  | PathAtom of hints_path_atom
  | PathStar of hints_path
  | PathSeq of hints_path * hints_path
  | PathOr of hints_path * hints_path
  | PathEmpty
  | PathEpsilon

type hint_term =
  | IsGlobRef of global_reference
  | IsConstr of constr * Univ.universe_context_set

type 'a gen_auto_tactic = {
  pri  : int;            (* A number lower is higher priority *)
  poly  : polymorphic;    (** Is the hint polymorpic and hence should be refreshed at each application *)
  pat  : constr_pattern option; (* A pattern for the concl of the Goal *)
  name  : hints_path_atom; (* A potential name to refer to the hint *) 
  code : 'a auto_tactic     (* the tactic to apply when the concl matches pat *)
}

type pri_auto_tactic = (constr * clausenv) gen_auto_tactic

type hint_entry = global_reference option * 
  (constr * types * Univ.universe_context_set) gen_auto_tactic

let eq_hints_path_atom p1 p2 = match p1, p2 with
| PathHints gr1, PathHints gr2 -> List.equal eq_gr gr1 gr2
| PathAny, PathAny -> true
| (PathHints _ | PathAny), _ -> false

let eq_auto_tactic t1 t2 = match t1, t2 with
| Res_pf (c1, _), Res_pf (c2, _) -> Constr.equal c1 c2
| ERes_pf (c1, _), ERes_pf (c2, _) -> Constr.equal c1 c2
| Give_exact (c1, _), Give_exact (c2, _) -> Constr.equal c1 c2
| Res_pf_THEN_trivial_fail (c1, _), Res_pf_THEN_trivial_fail (c2, _) -> Constr.equal c1 c2
| Unfold_nth gr1, Unfold_nth gr2 -> eq_egr gr1 gr2
| Extern tac1, Extern tac2 -> tac1 == tac2 (** May cause redundancy in addkv *)
| (Res_pf _ | ERes_pf _ | Give_exact _ | Res_pf_THEN_trivial_fail _
  | Unfold_nth _ | Extern _), _ -> false

let eq_gen_auto_tactic t1 t2 =
  Int.equal t1.pri t2.pri &&
  Option.equal constr_pattern_eq t1.pat t2.pat &&
  eq_hints_path_atom t1.name t2.name &&
  eq_auto_tactic t1.code t2.code

let pri_order_int (id1, {pri=pri1}) (id2, {pri=pri2}) =
  let d = pri1 - pri2 in
    if Int.equal d 0 then id2 - id1
    else d

let pri_order t1 t2 = pri_order_int t1 t2 <= 0

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

module Bounded_net = Btermdn.Make(struct
				    type t = stored_data
				    let compare = pri_order_int
				  end)

type search_entry = stored_data list * stored_data list * Bounded_net.t * bool array list


let empty_se = ([],[],Bounded_net.create (),[])

let eq_pri_auto_tactic (_, x) (_, y) =
  if Int.equal x.pri y.pri && Option.equal constr_pattern_eq x.pat y.pat then
    match x.code,y.code with
      | Res_pf (cstr,_),Res_pf (cstr1,_) -> 
	  Term.eq_constr cstr cstr1
      | ERes_pf (cstr,_),ERes_pf (cstr1,_) -> 
	  Term.eq_constr cstr cstr1
      | Give_exact (cstr,_),Give_exact (cstr1,_)  -> 
	  Term.eq_constr cstr cstr1
      | Res_pf_THEN_trivial_fail (cstr,_)
	  ,Res_pf_THEN_trivial_fail (cstr1,_) -> 
	  Term.eq_constr cstr cstr1
      | _,_ -> false
  else
    false

let add_tac pat t st (l,l',dn,m) =
  match pat with
  | None -> 
    if not (List.exists (eq_pri_auto_tactic t) l) then (List.insert pri_order t l, l', dn, m) 
    else (l, l', dn, m)
  | Some pat -> 
    if not (List.exists (eq_pri_auto_tactic t) l')
    then (l, List.insert pri_order t l', Bounded_net.add st dn (pat,t), m) else (l, l', dn, m)

let rebuild_dn st ((l,l',dn,m) : search_entry) =
  let dn' = 
    List.fold_left 
      (fun dn (id, t) -> Bounded_net.add (Some st) dn (Option.get t.pat, (id, t)))
      (Bounded_net.create ()) l'
  in
    (l, l', dn', m)

let lookup_tacs concl st (l,l',dn) =
  let l'  = Bounded_net.lookup st dn concl in
  let sl' = List.stable_sort pri_order_int l' in
    List.merge pri_order_int l sl'

module Constr_map = Map.Make(RefOrdered)

let is_transparent_gr (ids, csts) = function
  | VarRef id -> Id.Pred.mem id ids
  | ConstRef cst -> Cpred.mem cst csts
  | IndRef _ | ConstructRef _ -> false

let strip_params env c = 
  match kind_of_term c with
  | App (f, args) -> 
    (match kind_of_term f with
    | Const (p,_) ->
      let cb = lookup_constant p env in
	(match cb.Declarations.const_proj with
	| Some pb -> 
	  let n = pb.Declarations.proj_npars in
	    if Array.length args > n then
	      mkApp (mkProj (Projection.make p false, args.(n)), 
		     Array.sub args (n+1) (Array.length args - (n + 1)))
	    else c
	| None -> c)
    | _ -> c)
  | _ -> c

let instantiate_hint p =
  let mk_clenv c cty ctx =
    let env = Global.env () in
    let sigma = Evd.merge_context_set univ_flexible (Evd.from_env env) ctx in
    let cl = mk_clenv_from_env (Global.env()) sigma None (c,cty) in 
      {cl with templval = 
	  { cl.templval with rebus = strip_params env cl.templval.rebus };
	env = empty_env}
  in
  let code = match p.code with
    | Res_pf (c, cty, ctx) -> Res_pf (c, mk_clenv c cty ctx)
    | ERes_pf (c, cty, ctx) -> ERes_pf (c, mk_clenv c cty ctx)
    | Res_pf_THEN_trivial_fail (c, cty, ctx) ->
      Res_pf_THEN_trivial_fail (c, mk_clenv c cty ctx)
    | Give_exact (c, cty, ctx) -> Give_exact (c, mk_clenv c cty ctx)
    | Unfold_nth e -> Unfold_nth e
    | Extern t -> Extern t
  in { pri = p.pri; poly = p.poly; name = p.name; pat = p.pat; code = code }

let hints_path_atom_eq h1 h2 = match h1, h2 with
| PathHints l1, PathHints l2 -> List.equal eq_gr l1 l2
| PathAny, PathAny -> true
| _ -> false

let rec hints_path_eq h1 h2 = match h1, h2 with
| PathAtom h1, PathAtom h2 -> hints_path_atom_eq h1 h2
| PathStar h1, PathStar h2 -> hints_path_eq h1 h2
| PathSeq (l1, r1), PathSeq (l2, r2) ->
  hints_path_eq l1 l2 && hints_path_eq r1 r2
| PathOr (l1, r1), PathOr (l2, r2) ->
  hints_path_eq l1 l2 && hints_path_eq r1 r2
| PathEmpty, PathEmpty -> true
| PathEpsilon, PathEpsilon -> true
| _ -> false

let path_matches hp hints =
  let rec aux hp hints k =
    match hp, hints with
    | PathAtom _, [] -> false
    | PathAtom PathAny, (_ :: hints') -> k hints'
    | PathAtom p, (h :: hints') -> 
      if hints_path_atom_eq p h then k hints' else false
    | PathStar hp', hints -> 
      k hints || aux hp' hints (fun hints' -> aux hp hints' k)
    | PathSeq (hp, hp'), hints -> 
      aux hp hints (fun hints' -> aux hp' hints' k)
    | PathOr (hp, hp'), hints ->
      aux hp hints k || aux hp' hints k
    | PathEmpty, _ -> false
    | PathEpsilon, hints -> k hints
  in aux hp hints (fun hints' -> true)

let rec matches_epsilon = function
  | PathAtom _ -> false
  | PathStar _ -> true
  | PathSeq (p, p') -> matches_epsilon p && matches_epsilon p'
  | PathOr (p, p') -> matches_epsilon p || matches_epsilon p'
  | PathEmpty -> false
  | PathEpsilon -> true

let rec is_empty = function
  | PathAtom _ -> false
  | PathStar _ -> false
  | PathSeq (p, p') -> is_empty p || is_empty p'
  | PathOr (p, p') -> matches_epsilon p && matches_epsilon p'
  | PathEmpty -> true
  | PathEpsilon -> false

let rec path_derivate hp hint =
  let rec derivate_atoms hints hints' =
    match hints, hints' with
    | gr :: grs, gr' :: grs' when eq_gr gr gr' -> derivate_atoms grs grs'
    | [], [] -> PathEpsilon
    | [], hints -> PathEmpty
    | grs, [] -> PathAtom (PathHints grs)
    | _, _ -> PathEmpty 
  in
    match hp with
    | PathAtom PathAny -> PathEpsilon
    | PathAtom (PathHints grs) -> 
      (match grs, hint with
       | h :: hints, PathAny -> PathEmpty
       | hints, PathHints hints' -> derivate_atoms hints hints'
       | _, _ -> assert false)
    | PathStar p -> if path_matches p [hint] then hp else PathEpsilon
    | PathSeq (hp, hp') ->
      let hpder = path_derivate hp hint in
	if matches_epsilon hp then 
	  PathOr (PathSeq (hpder, hp'), path_derivate hp' hint)
	else if is_empty hpder then PathEmpty 
	else PathSeq (hpder, hp')
    | PathOr (hp, hp') ->
      PathOr (path_derivate hp hint, path_derivate hp' hint)
    | PathEmpty -> PathEmpty
    | PathEpsilon -> PathEmpty

let rec normalize_path h =
  match h with
  | PathStar PathEpsilon -> PathEpsilon
  | PathSeq (PathEmpty, _) | PathSeq (_, PathEmpty) -> PathEmpty
  | PathSeq (PathEpsilon, p) | PathSeq (p, PathEpsilon) -> normalize_path p
  | PathOr (PathEmpty, p) | PathOr (p, PathEmpty) -> normalize_path p
  | PathOr (p, q) -> 
    let p', q' = normalize_path p, normalize_path q in
      if hints_path_eq p p' && hints_path_eq q q' then h
      else normalize_path (PathOr (p', q'))
  | PathSeq (p, q) -> 
    let p', q' = normalize_path p, normalize_path q in
      if hints_path_eq p p' && hints_path_eq q q' then h
      else normalize_path (PathSeq (p', q'))
  | _ -> h

let path_derivate hp hint = normalize_path (path_derivate hp hint)

let rec pp_hints_path = function
  | PathAtom (PathAny) -> str"."
  | PathAtom (PathHints grs) -> pr_sequence pr_global grs
  | PathStar p -> str "(" ++ pp_hints_path p ++ str")*"
  | PathSeq (p, p') -> pp_hints_path p ++ str" ; " ++ pp_hints_path p'
  | PathOr (p, p') -> 
    str "(" ++ pp_hints_path p ++ spc () ++ str"|" ++ spc () ++ pp_hints_path p' ++ str ")"
  | PathEmpty -> str"Ø"
  | PathEpsilon -> str"ε"

let subst_path_atom subst p =
  match p with
  | PathAny -> p
  | PathHints grs ->
    let gr' gr = fst (subst_global subst gr) in
    let grs' = List.smartmap gr' grs in
      if grs' == grs then p else PathHints grs'

let rec subst_hints_path subst hp =
  match hp with
  | PathAtom p ->
    let p' = subst_path_atom subst p in
      if p' == p then hp else PathAtom p'
  | PathStar p -> let p' = subst_hints_path subst p in
      if p' == p then hp else PathStar p'
  | PathSeq (p, q) ->
    let p' = subst_hints_path subst p in
    let q' = subst_hints_path subst q in
      if p' == p && q' == q then hp else PathSeq (p', q')
  | PathOr (p, q) ->
    let p' = subst_hints_path subst p in
    let q' = subst_hints_path subst q in
      if p' == p && q' == q then hp else PathOr (p', q')
  | _ -> hp

module Hint_db = struct

  type t = {
    hintdb_state : Names.transparent_state;
    hintdb_cut : hints_path;
    hintdb_unfolds : Id.Set.t * Cset.t;
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
			  hintdb_cut = PathEmpty;
			  hintdb_unfolds = (Id.Set.empty, Cset.empty);
			  hintdb_max_id = 0;
			  use_dn = use_dn;
			  hintdb_map = Constr_map.empty;
			  hintdb_nopat = [] }

  let find key db =
    try Constr_map.find key db.hintdb_map
    with Not_found -> empty_se
 
  let realize_tac (id,tac) = tac

  let matches_mode args mode =
    Array.length args == Array.length mode &&
      Array.for_all2 (fun arg m -> not (m && occur_existential arg)) args mode
      
  let matches_modes args modes =
    if List.is_empty modes then true
    else List.exists (matches_mode args) modes

  let map_none db =
    List.map realize_tac (Sort.merge pri_order (List.map snd db.hintdb_nopat) [])
    
  let map_all k db =
    let (l,l',_,_) = find k db in
      List.map realize_tac (Sort.merge pri_order (List.map snd db.hintdb_nopat @ l) l')
	
  (** Precondition: concl has no existentials *)
  let map_auto (k,args) concl db =
    let (l,l',dn,m) = find k db in
    let st = if db.use_dn then  (Some db.hintdb_state) else None in
    let l' = lookup_tacs concl st (l,l',dn) in
      List.map realize_tac (Sort.merge pri_order (List.map snd db.hintdb_nopat) l')

  let map_existential (k,args) concl db =
    let (l,l',_,m) = find k db in
      if matches_modes args m then
	List.map realize_tac (Sort.merge pri_order (List.map snd db.hintdb_nopat @ l) l')
      else List.map realize_tac (List.map snd db.hintdb_nopat)

  (* [c] contains an existential *)
  let map_eauto (k,args) concl db =
    let (l,l',dn,m) = find k db in
      if matches_modes args m then
	let st = if db.use_dn then Some db.hintdb_state else None in
	let l' = lookup_tacs concl st (l,l',dn) in
	  List.map realize_tac (Sort.merge pri_order (List.map snd db.hintdb_nopat) l')
      else List.map realize_tac (List.map snd db.hintdb_nopat)

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
          (** ppedrot: this equality here is dubious. Maybe we can remove it? *)
          let is_present (_, (_, v')) = eq_gen_auto_tactic v v' in
	  if not (List.exists is_present db.hintdb_nopat) then
	    (** FIXME *)
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

  let add_one (k, v) db =
    let v = instantiate_hint v in
    let st',db,rebuild =
      match v.code with
      | Unfold_nth egr ->
	  let addunf (ids,csts) (ids',csts') =
	    match egr with
	    | EvalVarRef id -> (Id.Pred.add id ids, csts), (Id.Set.add id ids', csts')
	    | EvalConstRef cst -> (ids, Cpred.add cst csts), (ids', Cset.add cst csts')
	  in 
	  let state, unfs = addunf db.hintdb_state db.hintdb_unfolds in
	    state, { db with hintdb_unfolds = unfs }, true
      | _ -> db.hintdb_state, db, false
    in
    let db = if db.use_dn && rebuild then rebuild_db st' db else db
    in addkv k (next_hint_id db) v db

  let add_list l db = List.fold_left (fun db k -> add_one k db) db l

  let remove_sdl p sdl = List.smartfilter p sdl 
  let remove_he st p (sl1, sl2, dn, m as he) =
    let sl1' = remove_sdl p sl1 and sl2' = remove_sdl p sl2 in
      if sl1' == sl1 && sl2' == sl2 then he
      else rebuild_dn st (sl1', sl2', dn, m)

  let remove_list grs db =
    let filter (_, h) =
      match h.name with PathHints [gr] -> not (List.mem_f eq_gr gr grs) | _ -> true in
    let hintmap = Constr_map.map (remove_he db.hintdb_state filter) db.hintdb_map in
    let hintnopat = List.smartfilter (fun (ge, sd) -> filter sd) db.hintdb_nopat in
      { db with hintdb_map = hintmap; hintdb_nopat = hintnopat }

  let remove_one gr db = remove_list [gr] db

  let iter f db =
    f None [] (List.map (fun x -> realize_tac (snd x)) db.hintdb_nopat);
    Constr_map.iter (fun k (l,l',_,m) -> f (Some k) m (List.map realize_tac (l@l'))) db.hintdb_map

  let fold f db accu =
    let accu = f None [] (List.map (fun x -> snd (snd x)) db.hintdb_nopat) accu in
    Constr_map.fold (fun k (l,l',_,m) -> f (Some k) m (List.map snd (l@l'))) db.hintdb_map accu

  let transparent_state db = db.hintdb_state

  let set_transparent_state db st =
    if db.use_dn then rebuild_db st db
    else { db with hintdb_state = st }

  let add_cut path db =
    { db with hintdb_cut = normalize_path (PathOr (db.hintdb_cut, path)) }

  let add_mode gr m db =
    let (l,l',dn,ms) = find gr db in
      { db with hintdb_map = Constr_map.add gr (l,l',dn,m :: ms) db.hintdb_map }

  let cut db = db.hintdb_cut

  let unfolds db = db.hintdb_unfolds

  let use_dn db = db.use_dn

end

module Hintdbmap = String.Map

type hint_db = Hint_db.t

type hint_db_table = hint_db Hintdbmap.t ref

type hint_db_name = string

(** Initially created hint databases, for typeclasses and rewrite *)

let typeclasses_db = "typeclass_instances"
let rewrite_db = "rewrite"

let auto_init_db =
  Hintdbmap.add typeclasses_db (Hint_db.empty full_transparent_state true)
    (Hintdbmap.add rewrite_db (Hint_db.empty cst_full_transparent_state true)
       Hintdbmap.empty)

let searchtable : hint_db_table = ref auto_init_db

let searchtable_map name =
  Hintdbmap.find name !searchtable
let searchtable_add (name,db) =
  searchtable := Hintdbmap.add name db !searchtable
let current_db_names () = Hintdbmap.domain !searchtable
let current_db () = Hintdbmap.bindings !searchtable

let current_pure_db () =
  List.map snd (Hintdbmap.bindings (Hintdbmap.remove "v62" !searchtable))

let error_no_such_hint_database x =
  error ("No such Hint database: "^x^".")

(**************************************************************************)
(*                       Definition of the summary                        *)
(**************************************************************************)

let hints_init : (unit -> unit) ref = ref (fun () -> ())
let add_hints_init f =
  let init = !hints_init in
  hints_init := (fun () -> init (); f ())

let init     () = searchtable := auto_init_db; !hints_init ()
let freeze   _ = !searchtable
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

let make_exact_entry env sigma pri poly ?(name=PathAny) (c, cty, ctx) =
  let cty = strip_outer_cast cty in
    match kind_of_term cty with
    | Prod _ -> failwith "make_exact_entry"
    | _ ->
	let pat = snd (Patternops.pattern_of_constr env sigma cty) in
	let hd =
	  try head_pattern_bound pat
	  with BoundPattern -> failwith "make_exact_entry"
	in
          (Some hd,
	  { pri = (match pri with None -> 0 | Some p -> p);
	    poly = poly;
	    pat = Some pat;
	    name = name;
	    code = Give_exact (c, cty, ctx) })

let make_apply_entry env sigma (eapply,hnf,verbose) pri poly ?(name=PathAny) (c, cty, ctx) =
  let cty = if hnf then hnf_constr env sigma cty else cty in
    match kind_of_term cty with
    | Prod _ ->
        let sigma' = Evd.merge_context_set univ_flexible sigma ctx in
        let ce = mk_clenv_from_env env sigma' None (c,cty) in
	let c' = clenv_type (* ~reduce:false *) ce in
	let pat = snd (Patternops.pattern_of_constr env ce.evd c') in
        let hd =
	  try head_pattern_bound pat
          with BoundPattern -> failwith "make_apply_entry" in
        let nmiss = List.length (clenv_missing ce) in
	if Int.equal nmiss 0 then
	  (Some hd,
          { pri = (match pri with None -> nb_hyp cty | Some p -> p);
	    poly = poly;
            pat = Some pat;
	    name = name;
            code = Res_pf(c,cty,ctx) })
	else begin
	  if not eapply then failwith "make_apply_entry";
          if verbose then
	    msg_warning (str "the hint: eapply " ++ pr_lconstr c ++
	    str " will only be used by eauto");
          (Some hd,
           { pri = (match pri with None -> nb_hyp cty + nmiss | Some p -> p);
	     poly = poly;
             pat = Some pat;
	     name = name;
             code = ERes_pf(c,cty,ctx) })
        end
    | _ -> failwith "make_apply_entry"

(* flags is (e,h,v) with e=true if eapply and h=true if hnf and v=true if verbose
   c is a constr
   cty is the type of constr *)

let fresh_global_or_constr env sigma poly cr =
  match cr with
  | IsGlobRef gr -> Universes.fresh_global_instance env gr
  | IsConstr (c, ctx) -> (c, ctx)

let make_resolves env sigma flags pri poly ?name cr =
  let c, ctx = fresh_global_or_constr env sigma poly cr in
  let cty = Retyping.get_type_of env sigma c in
  let try_apply f =
    try Some (f (c, cty, ctx)) with Failure _ -> None in
  let ents = List.map_filter try_apply
    [make_exact_entry env sigma pri poly ?name; make_apply_entry env sigma flags pri poly ?name]
  in
  if List.is_empty ents then
    errorlabstrm "Hint"
      (pr_lconstr c ++ spc() ++
        (if pi1 flags then str"cannot be used as a hint."
	else str "can be used as a hint only for eauto."));
  ents

(* used to add an hypothesis to the local hint database *)
let make_resolve_hyp env sigma (hname,_,htyp) =
  try
    [make_apply_entry env sigma (true, true, false) None false
       ~name:(PathHints [VarRef hname])
       (mkVar hname, htyp, Univ.ContextSet.empty)]
  with
    | Failure _ -> []
    | e when Logic.catchable_exception e -> anomaly (Pp.str "make_resolve_hyp")

(* REM : in most cases hintname = id *)
let make_unfold eref =
  let g = global_of_evaluable_reference eref in
  (Some g,
   { pri = 4;
     poly = false;
     pat = None;
     name = PathHints [g];
     code = Unfold_nth eref })

let make_extern pri pat tacast =
  let hdconstr = Option.map try_head_pattern pat in
  (hdconstr,
   { pri = pri;
     poly = false;
     pat = pat;
     name = PathAny;
     code = Extern tacast })  

let make_mode ref m = 
  let ty = Global.type_of_global_unsafe ref in
  let ctx, t = decompose_prod ty in
  let n = List.length ctx in
  let m' = Array.of_list m in
    if not (n == Array.length m') then
      errorlabstrm "Hint"
	(pr_global ref ++ str" has " ++ int n ++ 
	   str" arguments while the mode declares " ++ int (Array.length m'))
    else m'
      
let make_trivial env sigma poly ?(name=PathAny) r =
  let c,ctx = fresh_global_or_constr env sigma poly r in
  let sigma = Evd.merge_context_set univ_flexible sigma ctx in
  let t = hnf_constr env sigma (type_of env sigma c) in
  let hd = head_of_constr_reference (head_constr t) in
  let ce = mk_clenv_from_env env sigma None (c,t) in
  (Some hd, { pri=1;
	      poly = poly;
              pat = Some (snd (Patternops.pattern_of_constr env ce.evd (clenv_type ce)));
	      name = name;
              code=Res_pf_THEN_trivial_fail(c,t,ctx) })



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
      | EvalVarRef v -> (if b then Id.Pred.add else Id.Pred.remove) v ids, csts)
      st grs
  in searchtable_add (dbname, Hint_db.set_transparent_state db st')

let remove_hint dbname grs =
  let db = get_db dbname in
  let db' = Hint_db.remove_list grs db in
    searchtable_add (dbname, db')

type hint_action =
  | CreateDB of bool * transparent_state
  | AddTransparency of evaluable_global_reference list * bool
  | AddHints of hint_entry list
  | RemoveHints of global_reference list
  | AddCut of hints_path
  | AddMode of global_reference * bool array

let add_cut dbname path =
  let db = get_db dbname in
  let db' = Hint_db.add_cut path db in
    searchtable_add (dbname, db')

let add_mode dbname l m =
  let db = get_db dbname in
  let db' = Hint_db.add_mode l m db in
    searchtable_add (dbname, db')

type hint_obj = bool * string * hint_action  (* locality, name, action *)

let cache_autohint (_,(local,name,hints)) =
  match hints with
  | CreateDB (b, st) -> searchtable_add (name, Hint_db.empty st b)
  | AddTransparency (grs, b) -> add_transparency name grs b
  | AddHints hints -> add_hint name hints
  | RemoveHints grs -> remove_hint name grs
  | AddCut path -> add_cut name path
  | AddMode (l, m) -> add_mode name l m

let subst_autohint (subst,(local,name,hintlist as obj)) =
  let subst_key gr =
    let (lab'', elab') = subst_global subst gr in
    let gr' =
      (try head_of_constr_reference (head_constr_bound elab')
       with Bound -> lab'')
    in if gr' == gr then gr else gr'
  in
  let subst_hint (k,data as hint) =
    let k' = Option.smartmap subst_key k in
    let pat' = Option.smartmap (subst_pattern subst) data.pat in
    let code' = match data.code with
      | Res_pf (c,t,ctx) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t'==t then data.code else Res_pf (c', t',ctx)
      | ERes_pf (c,t,ctx) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t'==t then data.code else ERes_pf (c',t',ctx)
      | Give_exact (c,t,ctx) ->
          let c' = subst_mps subst c in
	  let t' = subst_mps subst t in
          if c==c' && t'== t then data.code else Give_exact (c',t',ctx)
      | Res_pf_THEN_trivial_fail (c,t,ctx) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t==t' then data.code else Res_pf_THEN_trivial_fail (c',t',ctx)
      | Unfold_nth ref ->
          let ref' = subst_evaluable_reference subst ref in
          if ref==ref' then data.code else Unfold_nth ref'
      | Extern tac ->
	  let tac' = Tacsubst.subst_tactic subst tac in
	  if tac==tac' then data.code else Extern tac'
    in
    let name' = subst_path_atom subst data.name in
    let data' =
      if data.pat==pat' && data.name == name' && data.code==code' then data
      else { data with pat = pat'; name = name'; code = code' }
    in
    if k' == k && data' == data then hint else (k',data')
  in
    match hintlist with
    | CreateDB _ -> obj
    | AddTransparency (grs, b) ->
	let grs' = List.smartmap (subst_evaluable_reference subst) grs in
	  if grs==grs' then obj else (local, name, AddTransparency (grs', b))
    | AddHints hintlist ->
	let hintlist' = List.smartmap subst_hint hintlist in
	  if hintlist' == hintlist then obj else
	    (local,name,AddHints hintlist')
    | RemoveHints grs ->
	let grs' = List.smartmap (subst_global_reference subst) grs in
	  if grs==grs' then obj else (local, name, RemoveHints grs')
    | AddCut path ->
      let path' = subst_hints_path subst path in
	if path' == path then obj else (local, name, AddCut path')
    | AddMode (l,m) ->
      let l' = subst_global_reference subst l in
	(local, name, AddMode (l', m))

let classify_autohint ((local,name,hintlist) as obj) =
  match hintlist with
  | AddHints [] -> Dispose
  | _ -> if local then Dispose else Substitute obj

let inAutoHint : hint_obj -> obj =
  declare_object {(default_object "AUTOHINT") with
                    cache_function = cache_autohint;
		    load_function = (fun _ -> cache_autohint);
		    subst_function = subst_autohint;
		    classify_function = classify_autohint; }

let create_hint_db l n st b =
  Lib.add_anonymous_leaf (inAutoHint (l,n,CreateDB (b, st)))

let remove_hints local dbnames grs =
  let dbnames = if List.is_empty dbnames then ["core"] else dbnames in
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
     	      (List.flatten (List.map (fun (pri, poly, hnf, path, gr) ->
	        make_resolves env sigma (true,hnf,Flags.is_verbose()) 
		  pri poly ~name:path gr) clist)))))
    dbnames

let add_unfolds l local dbnames =
  List.iter
    (fun dbname -> Lib.add_anonymous_leaf
       (inAutoHint (local,dbname, AddHints (List.map make_unfold l))))
    dbnames

let add_cuts l local dbnames =
  List.iter
    (fun dbname -> Lib.add_anonymous_leaf
       (inAutoHint (local,dbname, AddCut l)))
    dbnames

let add_mode l m local dbnames =
  List.iter
    (fun dbname -> Lib.add_anonymous_leaf
      (let m' = make_mode l m in
	 (inAutoHint (local,dbname, AddMode (l,m')))))
    dbnames

let add_transparency l b local dbnames =
  List.iter
    (fun dbname -> Lib.add_anonymous_leaf
       (inAutoHint (local,dbname, AddTransparency (l, b))))
    dbnames

let add_extern pri pat tacast local dbname =
  let pat = match pat with
  | None -> None
  | Some (_, pat) -> Some pat
  in
  let hint = local, dbname, AddHints [make_extern pri pat tacast] in
  Lib.add_anonymous_leaf (inAutoHint hint)

let add_externs pri pat tacast local dbnames =
  List.iter (add_extern pri pat tacast local) dbnames

let add_trivials env sigma l local dbnames =
  List.iter
    (fun dbname ->
       Lib.add_anonymous_leaf (
	 inAutoHint(local,dbname, 
		    AddHints (List.map (fun (name, poly, c) -> make_trivial env sigma poly ~name c) l))))
    dbnames

let (forward_intern_tac, extern_intern_tac) = Hook.make ()

type hnf = bool

type hints_entry =
  | HintsResolveEntry of (int option * polymorphic * hnf * hints_path_atom * hint_term) list
  | HintsImmediateEntry of (hints_path_atom * polymorphic * hint_term) list
  | HintsCutEntry of hints_path
  | HintsUnfoldEntry of evaluable_global_reference list
  | HintsTransparencyEntry of evaluable_global_reference list * bool
  | HintsModeEntry of global_reference * bool list
  | HintsExternEntry of
      int * (patvar list * constr_pattern) option * glob_tactic_expr

let default_prepare_hint_ident = Id.of_string "H"

exception Found of constr * types

let prepare_hint check env init (sigma,c) =
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
      if not (Int.Set.is_empty (free_rels t)) then
	error "Hints with holes dependent on a bound variable not supported.";
      if occur_existential t then
	(* Not clever enough to construct dependency graph of evars *)
	error "Not clever enough to deal with evars dependent in other evars.";
      raise (Found (c,t))
    | _ -> iter_constr find_next_evar c in
  let rec iter c =
    try find_next_evar c; c
    with Found (evar,t) ->
      let id = next_ident_away_from default_prepare_hint_ident (fun id -> Id.Set.mem id !vars) in
      vars := Id.Set.add id !vars;
      subst := (evar,mkVar id)::!subst;
      mkNamedLambda id t (iter (replace_term evar (mkVar id) c)) in
  let c' = iter c in
    if check then Evarutil.check_evars (Global.env()) Evd.empty sigma c';
    let diff = Univ.ContextSet.diff (Evd.universe_context_set sigma) (Evd.universe_context_set init) in
      IsConstr (c', diff)

let interp_hints poly =
  fun h ->
  let f c =
    let evd,c = Constrintern.interp_open_constr (Global.env()) Evd.empty c in
      prepare_hint true (Global.env()) Evd.empty (evd,c) in
  let fref r =
    let gr = global_with_alias r in
    Dumpglob.add_glob (loc_of_reference r) gr;
    gr in
  let fr r = 
    evaluable_of_global_reference (Global.env()) (fref r)
  in
  let fi c =
    match c with
    | HintsReference c ->
      let gr = global_with_alias c in
	(PathHints [gr], poly, IsGlobRef gr)
    | HintsConstr c -> (PathAny, poly, f c)
  in
  let fres (pri, b, r) =
    let path, poly, gr = fi r in
      (pri, poly, b, path, gr)
  in
  let fp = Constrintern.intern_constr_pattern (Global.env()) in
  match h with
  | HintsResolve lhints -> HintsResolveEntry (List.map fres lhints)
  | HintsImmediate lhints -> HintsImmediateEntry (List.map fi lhints)
  | HintsUnfold lhints -> HintsUnfoldEntry (List.map fr lhints)
  | HintsTransparency (lhints, b) ->
      HintsTransparencyEntry (List.map fr lhints, b)
  | HintsMode (r, l) -> HintsModeEntry (fref r, l)
  | HintsConstructors lqid ->
      let constr_hints_of_ind qid =
        let ind = global_inductive_with_alias qid in
	let mib,_ = Global.lookup_inductive ind in
	Dumpglob.dump_reference (fst (qualid_of_reference qid)) "<>" (string_of_reference qid) "ind";
          List.init (nconstructors ind) 
	    (fun i -> let c = (ind,i+1) in
		      let gr = ConstructRef c in
			None, mib.Declarations.mind_polymorphic, true, 
			PathHints [gr], IsGlobRef gr)
      in HintsResolveEntry (List.flatten (List.map constr_hints_of_ind lqid))
  | HintsExtern (pri, patcom, tacexp) ->
      let pat =	Option.map fp patcom in
      let l = match pat with None -> [] | Some (l, _) -> l in
      let tacexp = Hook.get forward_intern_tac l tacexp in
      HintsExternEntry (pri, pat, tacexp)

let add_hints local dbnames0 h =
  if String.List.mem "nocore" dbnames0 then
    error "The hint database \"nocore\" is meant to stay empty.";
  let dbnames = if List.is_empty dbnames0 then ["core"] else dbnames0 in
  let env = Global.env() and sigma = Evd.empty in
  match h with
  | HintsResolveEntry lhints -> add_resolves env sigma lhints local dbnames
  | HintsImmediateEntry lhints -> add_trivials env sigma lhints local dbnames
  | HintsCutEntry lhints -> add_cuts lhints local dbnames
  | HintsModeEntry (l,m) -> add_mode l m local dbnames
  | HintsUnfoldEntry lhints -> add_unfolds lhints local dbnames
  | HintsTransparencyEntry (lhints, b) ->
      add_transparency lhints b local dbnames
  | HintsExternEntry (pri, pat, tacexp) ->
      add_externs pri pat tacexp local dbnames

let expand_constructor_hints env sigma lems =
  List.map_append (fun (evd,lem) ->
    match kind_of_term lem with
    | Ind (ind,u) ->
	List.init (nconstructors ind) 
	  (fun i -> IsConstr (mkConstructU ((ind,i+1),u), 
			      Univ.ContextSet.empty))
    | _ ->
	[prepare_hint false env sigma (evd,lem)]) lems

(* builds a hint database from a constr signature *)
(* typically used with (lid, ltyp) = pf_hyps_types <some goal> *)

let add_hint_lemmas env sigma eapply lems hint_db =
  let lems = expand_constructor_hints env sigma lems in
  let hintlist' =
    List.map_append (make_resolves env sigma (eapply,true,false) None true) lems in
  Hint_db.add_list hintlist' hint_db

let make_local_hint_db env sigma ts eapply lems =
  let sign = Environ.named_context env in
  let ts = match ts with
    | None -> Hint_db.transparent_state (searchtable_map "core") 
    | Some ts -> ts
  in
  let hintlist = List.map_append (make_resolve_hyp env sigma) sign in
  add_hint_lemmas env sigma eapply lems
    (Hint_db.add_list hintlist (Hint_db.empty ts false))

let make_local_hint_db = 
  if Flags.profile then
    let key = Profile.declare_profile "make_local_hint_db" in
      Profile.profile4 key make_local_hint_db
  else make_local_hint_db

let make_local_hint_db env sigma ?ts eapply lems =
  make_local_hint_db env sigma ts eapply lems

let make_db_list dbnames =
  let use_core = not (List.mem "nocore" dbnames) in
  let dbnames = List.remove String.equal "nocore" dbnames in
  let dbnames = if use_core then "core"::dbnames else dbnames in
  let lookup db =
    try searchtable_map db with Not_found -> error_no_such_hint_database db
  in
  List.map lookup dbnames

(**************************************************************************)
(*                    Functions for printing the hints                    *)
(**************************************************************************)

let pr_autotactic =
  function
  | Res_pf (c,clenv) -> (str"apply " ++ pr_constr c)
  | ERes_pf (c,clenv) -> (str"eapply " ++ pr_constr c)
  | Give_exact (c,clenv) -> (str"exact " ++ pr_constr c)
  | Res_pf_THEN_trivial_fail (c,clenv) ->
      (str"apply " ++ pr_constr c ++ str" ; trivial")
  | Unfold_nth c -> (str"unfold " ++  pr_evaluable_reference c)
  | Extern tac ->
      let env =
        try
          let (_, env) = Pfedit.get_current_goal_context () in
          env
        with e when Errors.noncritical e -> Global.env ()
      in
      (str "(*external*) " ++ Pptactic.pr_glob_tactic env tac)

let pr_hint (id, v) =
  (pr_autotactic v.code ++ str"(level " ++ int v.pri ++ str", id " ++ int id ++ str ")" ++ spc ())

let pr_hint_list hintlist =
  (str "  " ++ hov 0 (prlist pr_hint hintlist) ++ fnl ())

let pr_hints_db (name,db,hintlist) =
  (str "In the database " ++ str name ++ str ":" ++
     if List.is_empty hintlist then (str " nothing" ++ fnl ())
     else (fnl () ++ pr_hint_list hintlist))

(* Print all hints associated to head c in any database *)
let pr_hint_list_for_head c =
  let dbs = current_db () in
  let validate (name, db) =
    let hints = List.map (fun v -> 0, v) (Hint_db.map_all c db) in
    (name, db, hints)
  in
  let valid_dbs = List.map validate dbs in
  if List.is_empty valid_dbs then
    (str "No hint declared for :" ++ pr_global c)
  else
    hov 0
      (str"For " ++ pr_global c ++ str" -> " ++ fnl () ++
	 hov 0 (prlist pr_hints_db valid_dbs))

let pr_hint_ref ref = pr_hint_list_for_head ref

(* Print all hints associated to head id in any database *)

let pr_hint_term cl =
  try
    let dbs = current_db () in
    let valid_dbs =
      let fn = try
	  let hdc = decompose_app_bound cl in
	    if occur_existential cl then
	      Hint_db.map_existential hdc cl
	    else Hint_db.map_auto hdc cl
	with Bound -> Hint_db.map_none
      in
      let fn db = List.map (fun x -> 0, x) (fn db) in
      List.map (fun (name, db) -> (name, db, fn db)) dbs
    in
      if List.is_empty valid_dbs then
	(str "No hint applicable for current goal")
      else
	(str "Applicable Hints :" ++ fnl () ++
	    hov 0 (prlist pr_hints_db valid_dbs))
  with Match_failure _ | Failure _ ->
    (str "No hint applicable for current goal")

(* print all hints that apply to the concl of the current goal *)
let pr_applicable_hint () =
  let pts = get_pftreestate () in
  let glss = Proof.V82.subgoals pts in
  match glss.Evd.it with
  | [] -> Errors.error "No focused goal."
  | g::_ ->
    pr_hint_term (Goal.V82.concl glss.Evd.sigma g)

(* displays the whole hint database db *)
let pr_hint_db db =
  let pr_mode = prvect_with_sep spc (fun x -> if x then str"+" else str"-") in
  let pr_modes l = 
    if List.is_empty l then mt ()
    else str" (modes " ++ prlist_with_sep pr_comma pr_mode l ++ str")"
  in
  let content =
    let fold head modes hintlist accu =
      let goal_descr = match head with
      | None -> str "For any goal"
      | Some head -> str "For " ++ pr_global head ++ pr_modes modes
      in
      let hints = pr_hint_list (List.map (fun x -> (0, x)) hintlist) in
      let hint_descr = hov 0 (goal_descr ++ str " -> " ++ hints) in
      accu ++ hint_descr
    in
    Hint_db.fold fold db (mt ())
  in
  let (ids, csts) = Hint_db.transparent_state db in
  hov 0
    ((if Hint_db.use_dn db then str"Discriminated database"
      else str"Non-discriminated database")) ++ fnl () ++
  hov 2 (str"Unfoldable variable definitions: " ++ pr_idpred ids) ++ fnl () ++
  hov 2 (str"Unfoldable constant definitions: " ++ pr_cpred csts) ++ fnl () ++
  hov 2 (str"Cut: " ++ pp_hints_path (Hint_db.cut db)) ++ fnl () ++
  content

let pr_hint_db_by_name dbname =
  try
    let db = searchtable_map dbname in pr_hint_db db
  with Not_found ->
    error_no_such_hint_database dbname

(* displays all the hints of all databases *)
let pr_searchtable () =
  let fold name db accu =
    accu ++ str "In the database " ++ str name ++ str ":" ++ fnl () ++
    pr_hint_db db ++ fnl ()
  in
  Hintdbmap.fold fold !searchtable (mt ())

