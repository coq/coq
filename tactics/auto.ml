(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Inductive
open Evd
open Reduction
open Typing
open Pattern
open Tacmach
open Proof_type
open Pfedit
open Rawterm
open Evar_refiner
open Tacred
open Tactics
open Tacticals
open Clenv
open Hiddentac
open Libnames
open Nametab
open Libobject
open Library
open Printer
open Declarations
open Tacexpr

(****************************************************************************)
(*            The Type of Constructions Autotactic Hints                    *)
(****************************************************************************)

type auto_tactic = 
  | Res_pf     of constr * unit clausenv (* Hint Apply *)
  | ERes_pf    of constr * unit clausenv (* Hint EApply *)
  | Give_exact of constr                  
  | Res_pf_THEN_trivial_fail of constr * unit clausenv (* Hint Immediate *)
  | Unfold_nth of global_reference       (* Hint Unfold *)
  | Extern of raw_tactic_expr                (* Hint Extern *) 

type pri_auto_tactic = { 
  hname : identifier;    (* name of the hint *)
  pri  : int;            (* A number between 0 and 4, 4 = lower priority *)
  pat  : constr_pattern option; (* A pattern for the concl of the Goal *)
  code : auto_tactic     (* the tactic to apply when the concl matches pat *)
}

let pri_ord {pri=pri1} {pri=pri2} = pri1 - pri2

let pri_order {pri=pri1} {pri=pri2} = pri1 <= pri2

let insert v l = 
  let rec insrec = function
    | [] -> [v]
    | h::tl -> if pri_order v h then v::h::tl else h::(insrec tl)
  in 
  insrec l

(* Nov 98 -- Papageno *)
(* Les Hints sont r�-organis�s en plusieurs databases. 

  La table imp�rative "searchtable", de type "hint_db_table",
   associe une database (hint_db) � chaque nom.

  Une hint_db est une table d'association fonctionelle constr -> search_entry
  Le constr correspond � la constante de t�te de la conclusion.

  Une search_entry est un triplet comprenant :
     - la liste des tactiques qui n'ont pas de pattern associ�
     - la liste des tactiques qui ont un pattern
     - un discrimination net born� (Btermdn.t) constitu� de tous les
       patterns de la seconde liste de tactiques *)

type stored_data = pri_auto_tactic

type search_entry = stored_data list * stored_data list * stored_data Btermdn.t

let empty_se = ([],[],Btermdn.create ())

let add_tac t (l,l',dn) =
  match t.pat with
      None -> (insert t l, l', dn)
    | Some pat -> (l, insert t l', Btermdn.add dn (pat,t))


let lookup_tacs (hdc,c) (l,l',dn) =
  let l'  = List.map snd (Btermdn.lookup dn c) in
  let sl' = Sort.list pri_order l' in
    Sort.merge pri_order l sl'


module Constr_map = Map.Make(struct 
			       type t = constr_label
			       let compare = Pervasives.compare 
			     end)

module Hint_db = struct

  type t = search_entry Constr_map.t

  let empty = Constr_map.empty

  let find key db =
    try Constr_map.find key db
    with Not_found -> empty_se

  let map_all k db =
    let (l,l',_) = find k db in
      Sort.merge pri_order l l'
   
  let map_auto (k,c) db =
    lookup_tacs (k,c) (find k db)

  let add_one (k,v) db =
    let oval = find k db in 
      Constr_map.add k (add_tac v oval) db

  let add_list l db = List.fold_right add_one l db

  let iter f db = Constr_map.iter (fun k (l,l',_) -> f k (l@l')) db

end

type frozen_hint_db_table = Hint_db.t Stringmap.t 

type hint_db_table = Hint_db.t Stringmap.t ref

type hint_db_name = string

let searchtable = (ref Stringmap.empty : hint_db_table)

let searchtable_map name = 
  Stringmap.find name !searchtable
let searchtable_add (name,db) = 
  searchtable := Stringmap.add name db !searchtable

(**************************************************************************)
(*                       Definition of the summary                        *)
(**************************************************************************)

let init     () = searchtable := Stringmap.empty
let freeze   () = !searchtable
let unfreeze fs = searchtable := fs

let _ = Summary.declare_summary "search"
	  { Summary.freeze_function   = freeze;
	    Summary.unfreeze_function = unfreeze;
	    Summary.init_function     = init;
	    Summary.survive_section   = false }

 
(**************************************************************************)
(*             Auxiliary functions to prepare AUTOHINT objects            *)
(**************************************************************************)

let rec nb_hyp c = match kind_of_term c with
  | Prod(_,_,c2) -> if noccurn 1 c2 then 1+(nb_hyp c2) else nb_hyp c2
  | _ -> 0 

(* adding and removing tactics in the search table *)

let try_head_pattern c = 
  try head_pattern_bound c
  with BoundPattern -> error "Bound head variable"

let make_exact_entry name (c,cty) =
  let cty = strip_outer_cast cty in
  match kind_of_term cty with
    | Prod (_,_,_) -> 
	failwith "make_exact_entry"
    | _ ->
	(head_of_constr_reference (List.hd (head_constr cty)),
	   { hname=name; pri=0; pat=None; code=Give_exact c })

let make_apply_entry env sigma (eapply,verbose) name (c,cty) =
  let cty = hnf_constr env sigma cty in
  match kind_of_term cty with
    | Prod _ ->
        let ce = mk_clenv_from () (c,cty) in
	let c' = (clenv_template_type ce).rebus in
	let pat = Pattern.pattern_of_constr c' in
        let hd = (try head_pattern_bound pat
                  with BoundPattern -> failwith "make_apply_entry") in
        let nmiss = List.length (clenv_missing ce) 
        in 
	if eapply & (nmiss <> 0) then begin
          if verbose then 
	    warn (str "the hint: EApply " ++ prterm c ++
		    str " will only be used by EAuto"); 
          (hd,
           { hname = name;
	     pri = nb_hyp cty + nmiss;
             pat = Some pat;
             code = ERes_pf(c,ce) })
        end else 
	  (hd,
           { hname = name;
	     pri = nb_hyp cty;
             pat = Some pat;
             code = Res_pf(c,ce) })
    | _ -> failwith "make_apply_entry"
 
(* eap is (e,v) with e=true if eapply and v=true if verbose 
   c is a constr
   cty is the type of constr *)

let make_resolves env sigma name eap (c,cty) =
  let ents = 
    map_succeed 
      (fun f -> f name (c,cty)) 
      [make_exact_entry; make_apply_entry env sigma eap]
  in 
  if ents = [] then 
    errorlabstrm "Hint" (prterm c ++ spc () ++ str "cannot be used as a hint");
  ents

(* used to add an hypothesis to the local hint database *)
let make_resolve_hyp env sigma (hname,_,htyp) = 
  try
    [make_apply_entry env sigma (true, false) hname
       (mkVar hname, body_of_type htyp)]
  with 
    | Failure _ -> []
    | e when Logic.catchable_exception e -> anomaly "make_resolve_hyp"

(* REM : in most cases hintname = id *)
let make_unfold (hintname, ref) =
  (Pattern.label_of_ref ref,
   { hname = hintname;
     pri = 4;
     pat = None;
     code = Unfold_nth ref })

let make_extern name pri pat tacast = 
  let hdconstr = try_head_pattern pat in 
  (hdconstr,
   { hname = name;
     pri=pri;
     pat = Some pat;
     code= Extern tacast })

let make_trivial env sigma (name,c) =
  let t = hnf_constr env sigma (type_of env sigma c) in
  let hd = head_of_constr_reference (List.hd (head_constr t)) in
  let ce = mk_clenv_from () (c,t) in
  (hd, { hname = name;
	       pri=1;
               pat = Some (Pattern.pattern_of_constr (clenv_template_type ce).rebus);
               code=Res_pf_THEN_trivial_fail(c,ce) })

open Vernacexpr

(**************************************************************************)
(*               declaration of the AUTOHINT library object               *)
(**************************************************************************)

let eager o = ref (Lazy.Value o)

(* If the database does not exist, it is created *)
(* TODO: should a warning be printed in this case ?? *)
let add_hint dbname hintlist = 
  try 
    let db = searchtable_map dbname in
    let db' = Hint_db.add_list hintlist db in
    searchtable_add (dbname,db')
  with Not_found -> 
    let db = Hint_db.add_list hintlist Hint_db.empty in
    searchtable_add (dbname,db)

let cache_autohint (_,(name,l_hintlist)) =
  try add_hint name (Lazy.force l_hintlist) with _ -> anomaly "Auto.add_hint"

let subst_autohint (_,subst,((name,l_hintlist) as obj)) = 
  let recalc_hints hintlist =
    let env = Global.env() and sigma = Evd.empty in
    let recalc_hint ((_,data) as hint) =
      match data.code with
	| Res_pf (c,_) ->
	    let c' = Term.subst_mps subst c in
	      if c==c' then hint else
		make_apply_entry env sigma (false,false) 
		  data.hname (c', type_of env sigma c')
	| ERes_pf (c,_) ->
	    let c' = Term.subst_mps subst c in
	      if c==c' then hint else
		make_apply_entry env sigma (true,false) 
		  data.hname (c', type_of env sigma c')
	| Give_exact c ->
	    let c' = Term.subst_mps subst c in
	      if c==c' then hint else
		make_exact_entry data.hname (c',type_of env sigma c')
	| Res_pf_THEN_trivial_fail (c,_) ->
	    let c' = Term.subst_mps subst c in
	      if c==c' then hint else
		make_trivial env sigma (data.hname,c')
	| Unfold_nth ref -> 
	    let ref' = subst_global subst ref in
	      if ref==ref' then hint else
		make_unfold (data.hname,ref')
	| Extern _ ->
	    anomaly "Extern hints cannot be substituted!!!"
    in
      list_smartmap recalc_hint hintlist
  in
  let hintlist = Lazy.force l_hintlist in
    try
      let hintlist' = recalc_hints hintlist in
	if hintlist'==hintlist then
	  obj
	else
	  (name,eager hintlist')
    with
	_ -> (name,lazy (recalc_hints hintlist))

let classify_autohint (_,((name,l_hintlist) as obj)) =
  match Lazy.force l_hintlist with
      [] -> Dispose   
    | (_,{code=Extern _})::_ -> Dispose (* TODO! should be changed *)
    | _ -> Substitute obj

let export_autohint x = Some x

let (inAutoHint,outAutoHint) =
  declare_object {(default_object "AUTOHINT") with
                    cache_function = cache_autohint;
		    load_function = (fun _ -> cache_autohint);
		    subst_function = subst_autohint;
		    classify_function = classify_autohint;
                    export_function = export_autohint }


(**************************************************************************)
(*                     The "Hint" vernacular command                      *)
(**************************************************************************)
let add_resolves env sigma clist dbnames =
  List.iter 
    (fun dbname ->
       Lib.add_anonymous_leaf
	 (inAutoHint
	    (dbname,
	     let l =
     	       List.flatten
		 (List.map
		    (fun (name,c) -> 
		       let ty = type_of env sigma c in
		       let verbose = Options.is_verbose() in
			 make_resolves env sigma name (true,verbose) (c,ty)) clist
		 )
	     in
	       eager l
	    )))
    dbnames


let add_unfolds l dbnames =
  List.iter 
    (fun dbname -> Lib.add_anonymous_leaf 
       (inAutoHint (dbname, eager (List.map make_unfold l))))
    dbnames


let add_extern name pri (patmetas,pat) tacast dbname =
  (* We check that all metas that appear in tacast have at least
     one occurence in the left pattern pat *)
(* TODO
  let tacmetas = Coqast.collect_metas tacast in
*)
  let tacmetas = [] in
  match (list_subtract tacmetas patmetas) with
    | i::_ ->
	errorlabstrm "add_extern" 
	  (str "The meta-variable ?" ++ int i ++ str" is not bound")
    | []  ->
	Lib.add_anonymous_leaf
	  (inAutoHint(dbname, eager [make_extern name pri pat tacast]))

let add_externs name pri pat tacast dbnames = 
  List.iter (add_extern name pri pat tacast) dbnames


let add_trivials env sigma l dbnames =
  List.iter
    (fun dbname ->
       Lib.add_anonymous_leaf (
	 inAutoHint(dbname, eager (List.map (make_trivial env sigma) l))))
    dbnames


let add_hints dbnames h =
  let dbnames = if dbnames = [] then ["core"] else dbnames in match h with
  | HintsResolve lhints ->	
      let env = Global.env() and sigma = Evd.empty in
      let f (n,c) = 
	let c = Astterm.interp_constr sigma env c in
	let n = match n with
	  | None -> basename (sp_of_global None (Declare.reference_of_constr c))
	  | Some n -> n in
	(n,c) in
      add_resolves env sigma (List.map f lhints) dbnames
  | HintsImmediate lhints ->
      let env = Global.env() and sigma = Evd.empty in
      let f (n,c) = 
	let c = Astterm.interp_constr sigma env c in
	let n = match n with
	  | None -> basename (sp_of_global None (Declare.reference_of_constr c))
	  | Some n -> n in
	(n,c) in
      add_trivials env sigma (List.map f lhints) dbnames
  | HintsUnfold lhints ->
      let f (n,locqid) =
	let r = Nametab.global locqid in
	let n = match n with
	  | None -> basename (sp_of_global None r)
	  | Some n -> n in
	(n,r) in
      add_unfolds (List.map f lhints) dbnames
  | HintsConstructors (hintname, qid) ->
      let env = Global.env() and sigma = Evd.empty in
      let isp = global_inductive qid in
      let consnames = (snd (Global.lookup_inductive isp)).mind_consnames in
      let lcons = list_tabulate (fun i -> mkConstruct (isp,i+1)) (Array.length consnames) in
      let lcons = List.map2 (fun id c -> (id,c)) (Array.to_list consnames) lcons in
      add_resolves env sigma lcons dbnames
  | HintsExtern (hintname, pri, patcom, tacexp) ->
      let pat =	Astterm.interp_constrpattern Evd.empty (Global.env()) patcom in
      add_externs hintname pri pat tacexp dbnames

(**************************************************************************)
(*                    Functions for printing the hints                    *)
(**************************************************************************)

let fmt_autotactic = function
  | Res_pf (c,clenv) -> (str"Apply " ++ prterm c)
  | ERes_pf (c,clenv) -> (str"EApply " ++ prterm c)
  | Give_exact c -> (str"Exact " ++ prterm c)
  | Res_pf_THEN_trivial_fail (c,clenv) -> 
      (str"Apply " ++ prterm c ++ str" ; Trivial")
  | Unfold_nth c -> (str"Unfold " ++  pr_global c)
  | Extern coqast -> (str "Extern " ++ Pptactic.pr_raw_tactic coqast)

let fmt_hint v =
  (fmt_autotactic v.code ++ str"(" ++ int v.pri ++ str")" ++ spc ())

let fmt_hint_list hintlist =
  (str "  " ++ hov 0 (prlist fmt_hint hintlist) ++ fnl ())

let fmt_hints_db (name,db,hintlist) =
  (str "In the database " ++ str name ++ str ":" ++
     if hintlist = [] then (str " nothing" ++ fnl ())
     else (fnl () ++ fmt_hint_list hintlist))

(* Print all hints associated to head c in any database *)
let fmt_hint_list_for_head c = 
  let dbs = stringmap_to_list !searchtable in
  let valid_dbs = 
    map_succeed 
      (fun (name,db) -> (name,db,Hint_db.map_all c db)) 
      dbs 
  in
  if valid_dbs = [] then 
    (str "No hint declared for :" ++ pr_ref_label c)
  else 
    hov 0 
      (str"For " ++ pr_ref_label c ++ str" -> " ++ fnl () ++
	 hov 0 (prlist fmt_hints_db valid_dbs))

let fmt_hint_ref ref = fmt_hint_list_for_head (label_of_ref ref)

(* Print all hints associated to head id in any database *)
let print_hint_ref ref =  ppnl(fmt_hint_ref ref)

let fmt_hint_term cl = 
  try 
    let (hdc,args) = match head_constr_bound cl [] with 
      | hdc::args -> (hdc,args)
      | [] -> assert false 
    in
    let hd = head_of_constr_reference hdc in
    let dbs = stringmap_to_list !searchtable in
    let valid_dbs = 
      if occur_existential cl then 
	map_succeed 
	  (fun (name, db) -> (name, db, Hint_db.map_all hd db)) 
	  dbs
      else 
	map_succeed 
	  (fun (name, db) -> 
	     (name, db, Hint_db.map_auto (hd,applist(hdc,args)) db)) 
	  dbs
    in 
    if valid_dbs = [] then 
      (str "No hint applicable for current goal")
    else
      (str "Applicable Hints :" ++ fnl () ++
	 hov 0 (prlist fmt_hints_db valid_dbs))
  with Bound | Match_failure _ | Failure _ -> 
    (str "No hint applicable for current goal")
	  
let print_hint_term cl = ppnl (fmt_hint_term cl)

(* print all hints that apply to the concl of the current goal *)
let print_applicable_hint () = 
  let pts = get_pftreestate () in 
  let gl = nth_goal_of_pftreestate 1 pts in 
  print_hint_term (pf_concl gl)
    
(* displays the whole hint database db *)
let print_hint_db db =
  Hint_db.iter 
    (fun head hintlist ->
       msg (hov 0 
	      (str "For " ++ pr_ref_label head ++ str " -> " ++
		 fmt_hint_list hintlist)))
    db

let print_hint_db_by_name dbname =
  try 
    let db = searchtable_map dbname in print_hint_db db
  with Not_found -> 
    error (dbname^" : No such Hint database")
  
(* displays all the hints of all databases *)
let print_searchtable () =
  Stringmap.iter
    (fun name db ->
       msg (str "In the database " ++ str name ++ fnl ());
       print_hint_db db)
    !searchtable

(**************************************************************************)
(*                           Automatic tactics                            *)
(**************************************************************************)

(**************************************************************************)
(*          tactics with a trace mechanism for automatic search           *)
(**************************************************************************)

let priority l = List.map snd (List.filter (fun (pr,_) -> pr = 0) l)


(* Try unification with the precompiled clause, then use registered Apply *)

let unify_resolve (c,clenv) gls = 
  let (wc,kONT) = startWalk gls in
  let clenv' = connect_clenv wc clenv in
  let _ = clenv_unique_resolver false clenv' gls in  
  h_simplest_apply c gls

(* builds a hint database from a constr signature *)
(* typically used with (lid, ltyp) = pf_hyps_types <some goal> *)

let make_local_hint_db g = 
  let sign = pf_hyps g in
  let hintlist = list_map_append (make_resolve_hyp (pf_env g) (project g)) sign
  in Hint_db.add_list hintlist Hint_db.empty


(* Serait-ce possible de compiler d'abord la tactique puis de faire la
   substitution sans passer par bdize dont l'objectif est de pr�parer un
   terme pour l'affichage ? (HH) *)

(* Si on enl�ve le dernier argument (gl) conclPattern est calcul� une
fois pour toutes : en particulier si Pattern.somatch produit une UserError 
Ce qui fait que si la conclusion ne matche pas le pattern, Auto �choue, m�me
si apr�s Intros la conclusion matche le pattern.
*)

(* conclPattern doit �chouer avec error car il est rattraper par tclFIRST *)

let forward_tac_interp = 
  ref (fun _ -> failwith "tac_interp is not installed for Auto")

let set_extern_interp f = forward_tac_interp := f

let conclPattern concl pat tac gl =
  let constr_bindings =
    try Pattern.matches pat concl
    with PatternMatchingFailure -> error "conclPattern" in
  !forward_tac_interp constr_bindings tac gl

(**************************************************************************)
(*                           The Trivial tactic                           *)
(**************************************************************************)

(* local_db is a Hint database containing the hypotheses of current goal *)
(* Papageno : cette fonction a �t� pas mal simplifi�e depuis que la base
  de Hint imp�rative a �t� remplac�e par plusieurs bases fonctionnelles *)

let rec trivial_fail_db db_list local_db gl =
  let intro_tac = 
    tclTHEN intro 
      (fun g'->
	 let hintl = make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
	 in trivial_fail_db db_list (Hint_db.add_list hintl local_db) g')
  in
  tclFIRST 
    (assumption::intro_tac::
     (List.map tclCOMPLETE 
	(trivial_resolve db_list local_db (pf_concl gl)))) gl

and my_find_search db_list local_db hdc concl =
  let tacl = 
    if occur_existential concl then 
      list_map_append (fun db -> Hint_db.map_all hdc db) (local_db::db_list)
    else 
      list_map_append (fun db -> Hint_db.map_auto (hdc,concl) db)
      	(local_db::db_list)
  in
  List.map 
    (fun ({pri=b; pat=p; code=t} as patac) -> 
       (b,
	match t with
	  | Res_pf (term,cl)  -> unify_resolve (term,cl)
	  | ERes_pf (_,c) -> (fun gl -> error "eres_pf")
	  | Give_exact c  -> exact_no_check c
	  | Res_pf_THEN_trivial_fail (term,cl) -> 
	      tclTHEN 
		(unify_resolve (term,cl)) 
		(trivial_fail_db db_list local_db)
	  | Unfold_nth c -> unfold_constr c
	  | Extern tacast -> 
	      conclPattern concl (out_some p) tacast))
    tacl

and trivial_resolve db_list local_db cl = 
  try 
    let hdconstr = List.hd (head_constr_bound cl []) in
    priority 
      (my_find_search db_list local_db (head_of_constr_reference hdconstr) cl)
  with Bound | Not_found -> 
    []

let trivial dbnames gl =
  let db_list = 
    List.map
      (fun x -> 
	 try 
	   searchtable_map x
	 with Not_found -> 
	   error ("Trivial: "^x^": No such Hint database"))
      ("core"::dbnames) 
  in
  tclTRY (trivial_fail_db db_list (make_local_hint_db gl)) gl 
    
let full_trivial gl =
  let dbnames = stringmap_dom !searchtable in
  let dbnames = list_subtract dbnames ["v62"] in
  let db_list = List.map (fun x -> searchtable_map x) dbnames in
  tclTRY (trivial_fail_db db_list (make_local_hint_db gl)) gl

let gen_trivial = function
  | None -> full_trivial
  | Some l -> trivial l

let h_trivial l = Refiner.abstract_tactic (TacTrivial l) (gen_trivial l)

(**************************************************************************)
(*                       The classical Auto tactic                        *)
(**************************************************************************)

let possible_resolve db_list local_db cl =
  try 
    let hdconstr = List.hd (head_constr_bound cl []) in
    List.map snd 
      (my_find_search db_list local_db (head_of_constr_reference hdconstr) cl)
  with Bound | Not_found -> 
    []

let decomp_unary_term c gls = 
  let typc = pf_type_of gls c in 
  let hd = List.hd (head_constr typc) in 
  if Hipattern.is_conjunction hd then 
    simplest_case c gls 
  else 
    errorlabstrm "Auto.decomp_unary_term" (str "not a unary type") 

let decomp_empty_term c gls = 
  let typc = pf_type_of gls c in 
  let (hd,_) = decompose_app typc in 
  if Hipattern.is_empty_type hd then 
    simplest_case c gls 
  else 
    errorlabstrm "Auto.decomp_empty_term" (str "not an empty type") 


(* decomp is an natural number giving an indication on decomposition 
   of conjunction in hypotheses, 0 corresponds to no decomposition *)
(* n is the max depth of search *)
(* local_db contains the local Hypotheses *)

let rec search_gen decomp n db_list local_db extra_sign goal =
  if n=0 then error "BOUND 2";
  let decomp_tacs = match decomp with 
    | 0 -> [] 
    | p -> 
	(tclTRY_sign decomp_empty_term extra_sign)
	::
	(List.map 
	   (fun id -> tclTHENSEQ
               [decomp_unary_term (mkVar id);
                clear [id];
		search_gen decomp p db_list local_db []])
	   (pf_ids_of_hyps goal)) 
  in
  let intro_tac = 
    tclTHEN intro 
      (fun g' -> 
	 let (hid,_,htyp as d) = pf_last_hyp g' in
	 let hintl = 
	   try 
	     [make_apply_entry (pf_env g') (project g')
		(true,false) 
		hid (mkVar hid,body_of_type htyp)]
	   with Failure _ -> [] 
	 in
         search_gen decomp n db_list (Hint_db.add_list hintl local_db) [d] g') 
  in
  let rec_tacs = 
    List.map 
      (fun ntac -> 
	 tclTHEN ntac
	   (search_gen decomp (n-1) db_list local_db empty_named_context))
      (possible_resolve db_list local_db (pf_concl goal))
  in 
  tclFIRST (assumption::(decomp_tacs@(intro_tac::rec_tacs))) goal


let search = search_gen 0

let default_search_depth = ref 5
			     
let auto n dbnames gl = 
  let db_list = 
    List.map
      (fun x -> 
	 try 
	   searchtable_map x
	 with Not_found -> 
	   error ("Auto: "^x^": No such Hint database"))
      ("core"::dbnames) 
  in
  let hyps = pf_hyps gl in
  tclTRY (search n db_list (make_local_hint_db gl) hyps) gl

let default_auto = auto !default_search_depth []

let full_auto n gl = 
  let dbnames = stringmap_dom !searchtable in
  let dbnames = list_subtract dbnames ["v62"] in
  let db_list = List.map (fun x -> searchtable_map x) dbnames in
  let hyps = pf_hyps gl in
  tclTRY (search n db_list (make_local_hint_db gl) hyps) gl
  
let default_full_auto gl = full_auto !default_search_depth gl

let gen_auto n dbnames =
  let n = match n with None -> !default_search_depth | Some n -> n in
  match dbnames with
  | None -> full_auto n
  | Some l -> auto n l

let h_auto n l = Refiner.abstract_tactic (TacAuto (n,l)) (gen_auto n l)

(**************************************************************************)
(*                  The "destructing Auto" from Eduardo                   *)
(**************************************************************************)

(* Depth of search after decomposition of hypothesis, by default 
   one look for an immediate solution *) 
(* Papageno : de toute fa�on un param�te > 1 est trait� comme 1 pour 
   l'instant *)
let default_search_decomp = ref 1

let destruct_auto des_opt n gl = 
  let hyps = pf_hyps gl in
  search_gen des_opt n [searchtable_map "core"] 
    (make_local_hint_db gl) hyps gl
    
let dautomatic des_opt n = tclTRY (destruct_auto des_opt n)

let default_dauto = dautomatic !default_search_decomp !default_search_depth

let dauto = function
  | None, None     -> default_dauto
  | Some n, None   -> dautomatic !default_search_decomp n
  | Some n, Some p -> dautomatic p n
  | None, Some p   -> dautomatic p !default_search_depth

let h_dauto (n,p) = Refiner.abstract_tactic (TacDAuto (n,p)) (dauto (n,p))

(***************************************)
(*** A new formulation of Auto *********)
(***************************************)

type autoArguments =
  | UsingTDB       
  | Destructing   

let keepAfter tac1 tac2 = 
  (tclTHEN tac1 
     (function g -> tac2 [pf_last_hyp g] g))

let compileAutoArg contac = function
  | Destructing -> 
      (function g -> 
         let ctx = pf_hyps g in  
	 tclFIRST 
           (List.map 
              (fun (id,_,typ) -> 
                let cl = snd (decompose_prod (body_of_type typ)) in
                 if Hipattern.is_conjunction cl
		 then 
		   tclTHENSEQ [simplest_elim (mkVar id); clear [id]; contac] 
                 else 
		   tclFAIL 0) ctx) g)
  | UsingTDB ->  
      (tclTHEN  
         (Tacticals.tryAllClauses 
            (function 
               | Some id -> Dhyp.h_destructHyp false id
               | None    -> Dhyp.h_destructConcl))
         contac)

let compileAutoArgList contac = List.map (compileAutoArg contac)

let rec super_search n db_list local_db argl goal =
  if n = 0 then error "BOUND 2";
  tclFIRST
    (assumption
     ::
     (tclTHEN intro 
        (fun g -> 
	   let (hid,_,htyp) = pf_last_hyp g in
	   let hintl =
	     make_resolves (pf_env g) (project g)
	       hid (true,false) (mkVar hid,body_of_type htyp) in
	   super_search n db_list (Hint_db.add_list hintl local_db)
	     argl g))
     ::
     ((List.map 
         (fun ntac -> 
            tclTHEN ntac 
              (super_search (n-1) db_list local_db argl))
         (possible_resolve db_list local_db (pf_concl goal)))
      @
      (compileAutoArgList  
         (super_search (n-1) db_list local_db argl) argl))) goal

let search_superauto n to_add argl g = 
  let sigma =
    List.fold_right
      (fun (id,c) -> add_named_decl (id, None, pf_type_of g c))
      to_add empty_named_context in
  let db0 = list_map_append (make_resolve_hyp (pf_env g) (project g)) sigma in
  let db = Hint_db.add_list db0 (make_local_hint_db g) in
  super_search n [Stringmap.find "core" !searchtable] db argl g

let superauto n to_add argl  = 
  tclTRY (tclCOMPLETE (search_superauto n to_add argl))

let default_superauto g = superauto !default_search_depth [] [] g

let interp_to_add gl locqid =
  let r = Nametab.global locqid in
  let id = basename (sp_of_global None r) in
  (next_ident_away id (pf_ids_of_hyps gl), Declare.constr_of_reference r)

let gen_superauto nopt l a b gl =
  let n = match nopt with Some n -> n | None -> !default_search_depth in
  let al = (if a then [Destructing] else [])@(if b then [UsingTDB] else []) in
  superauto n (List.map (interp_to_add gl) l) al gl

let h_superauto no l a b =
  Refiner.abstract_tactic (TacSuperAuto (no,l,a,b)) (gen_superauto no l a b)

