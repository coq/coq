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
open Term
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
open Libobject
open Library
open Vernacinterp
open Printer

(****************************************************************************)
(*            The Type of Constructions Autotactic Hints                    *)
(****************************************************************************)

type auto_tactic = 
  | Res_pf     of constr * unit clausenv (* Hint Apply *)
  | ERes_pf    of constr * unit clausenv (* Hint EApply *)
  | Give_exact of constr                  
  | Res_pf_THEN_trivial_fail of constr * unit clausenv (* Hint Immediate *)
  | Unfold_nth of global_reference       (* Hint Unfold *)
  | Extern of Coqast.t                   (* Hint Extern *) 

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
(*               declaration of the AUTOHINT library object               *)
(**************************************************************************)

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

let cache_autohint (_,(name,hintlist)) =
  try add_hint name hintlist with _ -> anomaly "Auto.add_hint"

let export_autohint x = Some x

let (inAutoHint,outAutoHint) =
  declare_object ("AUTOHINT",
                  { load_function = (fun _ -> ());
                    cache_function = cache_autohint;
		    open_function = cache_autohint;
                    export_function = export_autohint })

(**************************************************************************)
(*                     The "Hint" vernacular command                      *)
(**************************************************************************)

let rec nb_hyp c = match kind_of_term c with
  | IsProd(_,_,c2) -> if dependent (mkRel 1) c2 then nb_hyp c2 else 1+(nb_hyp c2)
  | _ -> 0 

(* adding and removing tactics in the search table *)

let try_head_pattern c = 
  try head_pattern_bound c
  with BoundPattern -> error "Bound head variable"

let make_exact_entry name (c,cty) =
  let cty = strip_outer_cast cty in
  match kind_of_term cty with
    | IsProd (_,_,_) -> 
	failwith "make_exact_entry"
    | _ ->
	(head_of_constr_reference (List.hd (head_constr cty)),
	   { hname=name; pri=0; pat=None; code=Give_exact c })

let make_apply_entry env sigma (eapply,verbose) name (c,cty) =
  let cty = hnf_constr env sigma cty in
  match kind_of_term cty with
    | IsProd _ ->
        let ce = mk_clenv_from () (c,cty) in
	let c' = (clenv_template_type ce).rebus in
	let pat = Pattern.pattern_of_constr c' in
        let hd = (try head_pattern_bound pat
                  with BoundPattern -> failwith "make_apply_entry") in
        let nmiss = 
	  List.length 
            (clenv_missing ce (clenv_template ce,clenv_template_type ce)) 
        in 
	if eapply & (nmiss <> 0) then begin
          if verbose then 
	    wARN [< 'sTR "the hint: EApply "; prterm c;
		    'sTR " will only be used by EAuto" >]; 
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
    errorlabstrm "Hint" [< prterm c; 'sPC; 'sTR "cannot be used as a hint" >];
  ents

(* used to add an hypothesis to the local hint database *)
let make_resolve_hyp env sigma (hname,_,htyp) = 
  try
    [make_apply_entry env sigma (true, false) hname
       (mkVar hname, body_of_type htyp)]
  with 
    | Failure _ -> []
    | e when Logic.catchable_exception e -> anomaly "make_resolve_hyp"

let add_resolves env sigma clist dbnames =
  List.iter 
    (fun dbname ->
       Lib.add_anonymous_leaf
	 (inAutoHint
	    (dbname,
     	     (List.flatten
		(List.map
		   (fun (name,c) -> 
		      let ty = type_of env sigma c in
		      let verbose = Options.is_verbose() in
		      make_resolves env sigma name (true,verbose) (c,ty)) clist
		))
	    )))
    dbnames

let global qid =
  try Nametab.locate qid
  with Not_found -> Nametab.error_global_not_found_loc dummy_loc qid

(* REM : in most cases hintname = id *)
let make_unfold (hintname, ref) =
  (Pattern.label_of_ref ref,
   { hname = hintname;
     pri = 4;
     pat = None;
     code = Unfold_nth ref })

let add_unfolds l dbnames =
  List.iter 
    (fun dbname ->
       Lib.add_anonymous_leaf (inAutoHint (dbname, List.map make_unfold l)))
    dbnames

let make_extern name pri pat tacast = 
  let hdconstr = try_head_pattern pat in 
  (hdconstr,
   { hname = name;
     pri=pri;
     pat = Some pat;
     code= Extern tacast })

let add_extern name pri (patmetas,pat) tacast dbname =
  (* We check that all metas that appear in tacast have at least
     one occurence in the left pattern pat *)
  let tacmetas = Coqast.collect_metas tacast in 
  match (list_subtract tacmetas patmetas) with
    | i::_ ->
	errorlabstrm "add_extern" 
	  [< 'sTR "The meta-variable ?"; 'iNT i; 'sTR" is not bound" >]
    | []  ->
	Lib.add_anonymous_leaf
	  (inAutoHint(dbname, [make_extern name pri pat tacast]))

let add_externs name pri pat tacast dbnames = 
  List.iter (add_extern name pri pat tacast) dbnames

let make_trivial (name,c) =
  let sigma = Evd.empty and env = Global.env() in
  let t = hnf_constr env sigma (type_of env sigma c) in
  let hd = head_of_constr_reference (List.hd (head_constr t)) in
  let ce = mk_clenv_from () (c,t) in
  (hd, { hname = name;
	       pri=1;
               pat = Some (Pattern.pattern_of_constr (clenv_template_type ce).rebus);
               code=Res_pf_THEN_trivial_fail(c,ce) })

let add_trivials l dbnames =
  List.iter
    (fun dbname ->
       Lib.add_anonymous_leaf (inAutoHint(dbname, List.map make_trivial l)))
    dbnames

let _ = 
  vinterp_add
    "HintUnfold"
    (function 
       | [ VARG_IDENTIFIER hintname; VARG_VARGLIST l; VARG_QUALID qid] ->
	   let dbnames = if l = [] then ["core"] else 
	     List.map
	       (function VARG_IDENTIFIER i -> string_of_id i
		  | _ -> bad_vernac_args "HintUnfold") l in
      	   fun () -> 
	     let ref = global qid in
	     add_unfolds [(hintname, ref)] dbnames
       | _-> bad_vernac_args "HintUnfold")
    
let _ = 
  vinterp_add
    "HintResolve"
    (function 
       | [VARG_IDENTIFIER hintname; VARG_VARGLIST l; VARG_CONSTR c] ->
	   let env = Global.env() and sigma = Evd.empty in
	   let c1 = Astterm.interp_constr sigma env c in
	   let dbnames = if l = [] then ["core"] else 
	     List.map (function VARG_IDENTIFIER i -> string_of_id i
		      	 | _ -> bad_vernac_args "HintResolve") l in
	   fun () -> add_resolves env sigma [hintname, c1] dbnames
       | _-> bad_vernac_args "HintResolve" )
   
let _ = 
  vinterp_add
    "HintImmediate"
    (function 
       | [VARG_IDENTIFIER hintname; VARG_VARGLIST l; VARG_CONSTR c] ->
	   let c1 = Astterm.interp_constr Evd.empty (Global.env()) c in
	   let dbnames = if l = [] then ["core"] else 
	     List.map (function VARG_IDENTIFIER i -> string_of_id i
			 | _ -> bad_vernac_args "HintImmediate") l in
	   fun () -> add_trivials [hintname, c1] dbnames
       | _ -> bad_vernac_args "HintImmediate")


let _ = 
  vinterp_add
    "HintConstructors"
    (function 
       | [VARG_IDENTIFIER idr; VARG_VARGLIST l; VARG_QUALID qid] ->
	   begin 
	     try
	       let env = Global.env() and sigma = Evd.empty in
	       let isp = destMutInd (Declare.global_qualified_reference qid) in
	       let conspaths =
		 mis_conspaths (Global.lookup_mind_specif isp) in
	       let hyps = Declare.implicit_section_args (IndRef isp) in
	       let section_args = List.map (fun sp -> mkVar (basename sp)) hyps in
	       let lcons = 
		 array_map_to_list
		   (fun sp ->
		      let c = Declare.global_absolute_reference sp in
		      (basename sp, applist (c, section_args)))
		   conspaths in
	       let dbnames = if l = [] then ["core"] else 
	      	 List.map (function VARG_IDENTIFIER i -> string_of_id i
			     | _ -> bad_vernac_args "HintConstructors") l in
    	       fun () -> add_resolves env sigma lcons dbnames
	     with Invalid_argument("mind_specif_of_mind") -> 
	       error ((Nametab.string_of_qualid qid) ^ " is not an inductive type")
	   end 
       | _ -> bad_vernac_args "HintConstructors")
    
let _ = 
  vinterp_add
    "HintExtern"
    (function 
       | [VARG_IDENTIFIER hintname; VARG_VARGLIST l;
	  VARG_NUMBER pri; VARG_CONSTR patcom; VARG_TACTIC tacexp] ->
           let pat =
	     Astterm.interp_constrpattern Evd.empty (Global.env()) patcom in
	   let dbnames = if l = [] then ["core"] else 
	     List.map (function VARG_IDENTIFIER i -> string_of_id i
		      	 | _ -> bad_vernac_args "HintConstructors") l in
           fun () -> add_externs hintname pri pat tacexp dbnames
       | _ -> bad_vernac_args "HintExtern")

let _ = 
  vinterp_add
    "HintsResolve"
    (function
       | (VARG_VARGLIST l)::lh ->
	   let env = Global.env() and sigma = Evd.empty in
 	   let lhints = 
	     List.map
	       (function
		  | VARG_QUALID qid -> 
		      let ref = global qid in
		      let env = Global.env() in
		      let c = Declare.constr_of_reference Evd.empty env ref in
		      let hyps = Declare.implicit_section_args ref in
		      let section_args = List.map (fun sp -> mkVar (basename sp)) hyps in
		      let _,i = Nametab.repr_qualid qid in
		      (i, applist (c,section_args))
		  | _-> bad_vernac_args "HintsResolve") lh in
	   let dbnames = if l = [] then ["core"] else 
	     List.map (function VARG_IDENTIFIER i -> string_of_id i
		      	 | _-> bad_vernac_args "HintsResolve") l in
	   fun () -> add_resolves env sigma lhints dbnames
       | _-> bad_vernac_args "HintsResolve")
    
let _ = 
  vinterp_add
    "HintsUnfold"
    (function
       | (VARG_VARGLIST l)::lh ->
	   let lhints = 
	     List.map (function
			 | VARG_QUALID qid ->
			     let _,n = Nametab.repr_qualid qid in
			     (n, global qid)
		      	 | _ -> bad_vernac_args "HintsUnfold") lh in
	   let dbnames = if l = [] then ["core"] else 
	     List.map (function 
			 | VARG_IDENTIFIER i -> string_of_id i
		      	 | _ -> bad_vernac_args "HintsUnfold") l in
	   fun () -> add_unfolds lhints dbnames
       | _ -> bad_vernac_args "HintsUnfold")
    
let _ = 
  vinterp_add
    "HintsImmediate"
    (function
       | (VARG_VARGLIST l)::lh ->
	   let lhints = 
	     List.map
	       (function
		  | VARG_QUALID qid -> 
		      let _,n = Nametab.repr_qualid qid in
		      let ref = Nametab.locate qid in
		      let env = Global.env () in
		      let c = Declare.constr_of_reference Evd.empty env ref in
		      let hyps = Declare.implicit_section_args ref in
		      let section_args = List.map (fun sp -> mkVar (basename sp)) hyps in
		      (n, applist (c, section_args))
		  | _ -> bad_vernac_args "HintsImmediate") lh in
	   let dbnames = if l = [] then ["core"] else 
	     List.map (function 
			 | VARG_IDENTIFIER i -> string_of_id i
		      	 | _ -> bad_vernac_args "HintsImmediate") l in
	   fun () -> add_trivials lhints dbnames
       | _-> bad_vernac_args "HintsImmediate")
    
(**************************************************************************)
(*                    Functions for printing the hints                    *)
(**************************************************************************)

let fmt_autotactic = function
  | Res_pf (c,clenv) -> [< 'sTR"Apply "; prterm c >]
  | ERes_pf (c,clenv) -> [< 'sTR"EApply "; prterm c >]
  | Give_exact c -> [< 'sTR"Exact " ; prterm c >]
  | Res_pf_THEN_trivial_fail (c,clenv) -> 
      [< 'sTR"Apply "; prterm c ; 'sTR" ; Trivial" >]
  | Unfold_nth c -> [< 'sTR"Unfold " ;  pr_global c >]
  | Extern coqast -> [< 'sTR "Extern "; gentacpr coqast >]

let fmt_hint v =
  [< fmt_autotactic v.code; 'sTR"("; 'iNT v.pri; 'sTR")"; 'sPC >]

let fmt_hint_list hintlist =
  [< 'sTR "  "; hOV 0 (prlist fmt_hint hintlist); 'fNL >]

let fmt_hints_db (name,db,hintlist) =
  [< 'sTR "In the database "; 'sTR name; 'sTR ":";
     if hintlist = [] then [< 'sTR " nothing"; 'fNL >]
     else [< 'fNL; fmt_hint_list hintlist >] >]

(* Print all hints associated to head c in any database *)
let fmt_hint_list_for_head c = 
  let dbs = stringmap_to_list !searchtable in
  let valid_dbs = 
    map_succeed 
      (fun (name,db) -> (name,db,Hint_db.map_all c db)) 
      dbs 
  in
  if valid_dbs = [] then 
    [<'sTR "No hint declared for :"; pr_ref_label c >]
  else 
    hOV 0 
      [< 'sTR"For "; pr_ref_label c; 'sTR" -> "; 'fNL;
	 hOV 0 (prlist fmt_hints_db valid_dbs) >]

let fmt_hint_id id = 
  try 
    let c = Declare.global_reference CCI id in
    fmt_hint_list_for_head (head_of_constr_reference c)
  with Not_found -> 
    [< pr_id id; 'sTR " not declared" >]

(* Print all hints associated to head id in any database *)
let print_hint_id id =  pPNL(fmt_hint_id id)

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
      [<'sTR "No hint applicable for current goal" >]
    else
      [< 'sTR "Applicable Hints :"; 'fNL;
	 hOV 0 (prlist fmt_hints_db valid_dbs) >]
  with Bound | Match_failure _ | Failure _ -> 
    [<'sTR "No hint applicable for current goal" >]
	  
let print_hint_term cl = pPNL (fmt_hint_term cl)

(* print all hints that apply to the concl of the current goal *)
let print_applicable_hint () = 
  let pts = get_pftreestate () in 
  let gl = nth_goal_of_pftreestate 1 pts in 
  print_hint_term (pf_concl gl)
    
(* displays the whole hint database db *)
let print_hint_db db =
  Hint_db.iter 
    (fun head hintlist ->
       mSG (hOV 0 
	      [< 'sTR "For "; pr_ref_label head; 'sTR " -> ";
		 fmt_hint_list hintlist >]))
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
       mSG [< 'sTR "In the database "; 'sTR name; 'fNL >];
       print_hint_db db)
    !searchtable

let _ = 
  vinterp_add "PrintHint"
    (function 
       | [] -> fun () -> print_searchtable()
       | _ -> bad_vernac_args "PrintHint")

let _ = 
  vinterp_add "PrintHintDb"
    (function 
       | [(VARG_IDENTIFIER id)] -> 
	   fun () -> print_hint_db_by_name (string_of_id id)
       | _ -> bad_vernac_args "PrintHintDb")

let _ = 
  vinterp_add "PrintHintGoal"
    (function 
       | [] -> fun () -> print_applicable_hint()
       | _ -> bad_vernac_args "PrintHintGoal")
    
let _ = 
  vinterp_add "PrintHintId"
    (function 
       | [(VARG_IDENTIFIER id)] -> fun () -> print_hint_id id
       | _ -> bad_vernac_args "PrintHintId")

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


(**************************************************************************)
(*                           The Trivial tactic                           *)
(**************************************************************************)

(* local_db is a Hint database containing the hypotheses of current goal *)
(* Papageno : cette fonction a été pas mal simplifiée depuis que la base
  de Hint impérative a été remplacée par plusieurs bases fonctionnelles *)

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

let dyn_trivial = function
  | []                  -> trivial []
  | [Quoted_string "*"] -> full_trivial
  | l -> trivial (List.map 
		    (function 
		       | Identifier id -> (string_of_id id)
		       | other -> bad_tactic_args "dyn_trivial" [other]) 
		    l)
   
let h_trivial = hide_tactic "Trivial" dyn_trivial

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
    errorlabstrm "Auto.decomp_unary_term" [<'sTR "not a unary type" >] 

let decomp_empty_term c gls = 
  let typc = pf_type_of gls c in 
  let (hd,_) = decomp_app typc in 
  if Hipattern.is_empty_type hd then 
    simplest_case c gls 
  else 
    errorlabstrm "Auto.decomp_empty_term" [<'sTR "not an empty type" >] 


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
	   (fun id -> tclTHEN (decomp_unary_term (mkVar id)) 
		(tclTHEN 
		   (clear_one id)
		   (search_gen decomp p db_list local_db [])))
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

let dyn_auto l = match l with
  | []          -> auto !default_search_depth []
  | [Integer n] -> auto n []
  | [Quoted_string "*"] -> default_full_auto 
  | [Integer n; Quoted_string "*"] -> full_auto n
  | (Integer n)::l1 -> 
      auto n (List.map 
		(function 
		   | Identifier id -> (string_of_id id)
		   | other -> bad_tactic_args "dyn_auto" [other]) l1)
  | _ -> 
      auto !default_search_depth 
	(List.map 
	   (function 
	      | Identifier id -> (string_of_id id)
	      | other -> bad_tactic_args "dyn_auto" [other]) l)

let h_auto = hide_tactic "Auto" dyn_auto 

(**************************************************************************)
(*                  The "destructing Auto" from Eduardo                   *)
(**************************************************************************)

(* Depth of search after decomposition of hypothesis, by default 
   one look for an immediate solution *) 
(* Papageno : de toute façon un paramète > 1 est traité comme 1 pour 
   l'instant *)
let default_search_decomp = ref 1

let destruct_auto des_opt n gl = 
  let hyps = pf_hyps gl in
  search_gen des_opt n [searchtable_map "core"] 
    (make_local_hint_db gl) hyps gl
    
let dautomatic des_opt n = tclTRY (destruct_auto des_opt n)

let default_dauto = dautomatic !default_search_decomp !default_search_depth

let dyn_dauto = function
  | []          -> default_dauto
  | [Integer n] -> dautomatic !default_search_decomp n
  | [Integer n; Integer p] -> dautomatic p n
  | _           -> invalid_arg "DAuto: non numeric arguments"
     
let dauto =
  let gentac = hide_tactic "DAuto" dyn_dauto in
  function
    | (None, None)     -> gentac []
    | (Some n, None)   -> gentac [Integer n]
    | (Some n, Some p) -> gentac [Integer n; Integer p]
    | _ -> assert false

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
                 if (Hipattern.is_conjunction (hd_of_prod (body_of_type typ)))
		 then 
		   (tclTHEN
                      (tclTHEN (simplest_elim (mkVar id)) 
                         (clear_one id))
                      contac) 
                 else 
		   tclFAIL 0) ctx) g)
  | UsingTDB ->  
      (tclTHEN  
         (Tacticals.tryAllClauses 
            (function 
               | Some id -> Dhyp.dHyp id
               | None    -> Dhyp.dConcl))
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
      (fun (id,c) -> add_named_assum (id, pf_type_of g c))
      to_add empty_named_context in
  let db0 = list_map_append (make_resolve_hyp (pf_env g) (project g)) sigma in
  let db = Hint_db.add_list db0 (make_local_hint_db g) in
  super_search n [Stringmap.find "core" !searchtable] db argl g

let superauto n to_add argl  = 
  tclTRY (tclCOMPLETE (search_superauto n to_add argl))

let default_superauto g = superauto !default_search_depth [] [] g

let cvt_autoArg = function
  | "Destructing"  -> [Destructing]
  | "UsingTDB"     -> [UsingTDB]
  | "NoAutoArg"    -> []
  | x -> errorlabstrm "cvt_autoArg"
        [< 'sTR "Unexpected argument for Auto!"; 'sTR x >]

let cvt_autoArgs =
  list_join_map
    (function 
       | Quoted_string s -> (cvt_autoArg s)
       | _ -> errorlabstrm "cvt_autoArgs" [< 'sTR "String expected" >])

let interp_to_add gl = function
  | Qualid qid ->
      let _,id = Nametab.repr_qualid qid in
      (next_ident_away id (pf_ids_of_hyps gl), 
       Declare.constr_of_reference Evd.empty (Global.env()) (global qid))
  | _ -> errorlabstrm "cvt_autoArgs" [< 'sTR "Qualid expected" >]

let dyn_superauto l g = 
  match l with
    | (Integer n)::a::b::c::to_add ->
        superauto n (List.map (interp_to_add g) to_add) (cvt_autoArgs [a;b;c])g
    | _::a::b::c::to_add  -> 
        superauto !default_search_depth (List.map (interp_to_add g) to_add)
	  (cvt_autoArgs [a;b;c]) g
    | l -> bad_tactic_args "SuperAuto" l g

let h_superauto = hide_tactic "SuperAuto" dyn_superauto
