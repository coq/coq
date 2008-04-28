(* Une tactique qui tente de démontrer toute seule le but courant,
   interruptible par pcoq (si dans le fichier C:\WINDOWS\free il y a un A)
*)
open Termops;;
open Nameops;;
open Auto;;
open Clenv;;
open Command;;
open Declarations;;
open Declare;;
open Eauto;;
open Environ;;
open Equality;;
open Evd;;
open Hipattern;;
open Inductive;;
open Names;;
open Pattern;;
open Pbp;;
open Pfedit;;
open Pp;;
open Printer
open Proof_trees;;
open Proof_type;;
open Rawterm;;
open Reduction;;
open Refiner;;
open Sign;;
open String;;
open Tacmach;;
open Tacred;;
open Tacticals;;
open Tactics;;
open Term;;
open Typing;;
open Util;;
open Vernacentries;;
open Vernacinterp;;


let parse_com   = Pcoq.parse_string Pcoq.Constr.constr;;
let parse_tac  t =
    try (Pcoq.parse_string Pcoq.Tactic.tactic t)
    with _ -> (msgnl (hov 0 (str"pas parsé: " ++ str t));
	       failwith "tactic")
;;

let is_free () =
   let st =open_in_bin ((Sys.getenv "HOME")^"/.free") in
   let c=input_char st in
   close_in st;
   c = 'A'
;;

(* marche pas *)
(*
let is_free () =
   msgnl (hov 0 [< 'str"Isfree========= "; 'fNL >]);
   let s = Stream.of_channel stdin in
   msgnl (hov 0 [< 'str"Isfree s "; 'fNL >]);
   try (Stream.empty s;
        msgnl (hov 0 [< 'str"Isfree empty "; 'fNL >]);
        true)
   with _ -> (msgnl (hov 0 [< 'str"Isfree not empty "; 'fNL >]);
              false)
;;
*)
let free_try tac g =
    if is_free()
    then (tac g)
    else (failwith "not free")
;;
let adrel (x,t) e =
    match x with 
      Name(xid) -> Environ.push_rel (x,None,t) e
    | Anonymous -> Environ.push_rel (x,None,t) e
(* les constantes ayant une définition apparaissant dans x *)
let rec def_const_in_term_rec vl x = 
     match (kind_of_term x) with
     Prod(n,t,c)->
        let vl = (adrel (n,t) vl) in def_const_in_term_rec vl c
   | Lambda(n,t,c) ->
        let vl = (adrel (n,t) vl) in def_const_in_term_rec vl c
   | App(f,args) -> def_const_in_term_rec vl f
   | Sort(Prop(Null)) -> Prop(Null)
   | Sort(c) -> c
   | Ind(ind) ->
          let (mib, mip) = Global.lookup_inductive ind in
	  new_sort_in_family (inductive_sort_family mip)
   | Construct(c) ->
          def_const_in_term_rec vl (mkInd (inductive_of_constructor c))
   | Case(_,x,t,a) 
        -> def_const_in_term_rec vl x
   | Cast(x,_,t)-> def_const_in_term_rec vl t
   | Const(c)  -> def_const_in_term_rec vl (Typeops.type_of_constant vl c)
   | _ -> def_const_in_term_rec vl (type_of vl Evd.empty x)
;;
let def_const_in_term_ x =
    def_const_in_term_rec  (Global.env()) (strip_outer_cast x)
;;
(*************************************************************************
 recopiés de refiner.ml, car print_subscript pas exportée dans refiner.mli 
 modif de print_info_script avec pr_bar
*)

let pr_bar () = str "|"

let rec print_info_script sigma osign pf =
  let {evar_hyps=sign; evar_concl=cl} = pf.goal in
  match pf.ref with
    | None -> (mt ())
    | Some(r,spfl) ->
        Tactic_printer.pr_rule r ++
           match spfl with
             | [] ->
		   (str " " ++ fnl())
             | [pf1] ->
                 if pf1.ref = None then 
		   (str " " ++ fnl())
                 else 
		   (str";" ++ brk(1,3) ++
		      print_info_script sigma sign pf1)
             | _ -> ( str";[" ++ fnl() ++
                       prlist_with_sep pr_bar
                         (print_info_script sigma sign) spfl ++
                       str"]")

let format_print_info_script sigma osign pf = 
  hov 0 (print_info_script sigma osign pf)
    
let print_subscript sigma sign pf = 
 (* if is_tactic_proof pf then 
    format_print_info_script sigma sign (subproof_of_proof pf)
  else *)
    format_print_info_script sigma sign pf
(****************)

let pp_string x =
   msgnl_with Format.str_formatter x;
   Format.flush_str_formatter ()
;;

(***********************************************************************
   copié de tactics/eauto.ml
*)

(***************************************************************************)
(* A tactic similar to Auto, but using EApply, Assumption and e_give_exact *)
(***************************************************************************)

let unify_e_resolve  (c,clenv) gls = 
  let clenv' = connect_clenv gls clenv in
  let _ = clenv_unique_resolver false clenv' gls in
    Hiddentac.h_simplest_eapply c gls

let rec e_trivial_fail_db db_list local_db goal =
  let tacl = 
    registered_e_assumption ::
    (tclTHEN Tactics.intro 
       (function g'->
	  let d = pf_last_hyp g' in
	  let hintl = make_resolve_hyp (pf_env g') (project g') d in
          (e_trivial_fail_db db_list
	     (add_hint_list hintl local_db) g'))) ::
    (List.map fst (e_trivial_resolve db_list local_db (pf_concl goal)) )
  in 
  tclFIRST (List.map tclCOMPLETE tacl) goal 

and e_my_find_search db_list local_db hdc concl = 
  let hdc = head_of_constr_reference hdc in
  let flags = Auto.auto_unif_flags in
  let hintl =
    if occur_existential concl then 
      list_map_append (fun (st, db) -> List.map (fun x -> ({flags with Unification.modulo_delta = st}, x))
	(Hint_db.map_all hdc db)) (local_db::db_list)
    else 
      list_map_append (fun (st, db) -> List.map (fun x -> ({flags with Unification.modulo_delta = st}, x)) 
	(Hint_db.map_auto (hdc,concl) db)) (local_db::db_list)
  in 
  let tac_of_hint = 
    fun (st, ({pri=b; pat = p; code=t} as _patac)) -> 
      (b, 
       let tac =
	 match t with
	   | Res_pf (term,cl) -> unify_resolve st (term,cl)
	   | ERes_pf (term,cl) -> unify_e_resolve (term,cl)
	   | Give_exact (c) -> e_give_exact_constr c
	   | Res_pf_THEN_trivial_fail (term,cl) ->
               tclTHEN (unify_e_resolve (term,cl)) 
		 (e_trivial_fail_db db_list local_db)
	   | Unfold_nth c -> unfold_in_concl [[],c]
	   | Extern tacast -> Auto.conclPattern concl 
	       (Option.get p) tacast
       in 
       (free_try tac,fmt_autotactic t))
       (*i
	 fun gls -> pPNL (fmt_autotactic t); Format.print_flush (); 
                     try tac gls
		     with e when Logic.catchable_exception(e) -> 
                            (Format.print_string "Fail\n"; 
			     Format.print_flush (); 
			     raise e)
       i*)
  in 
  List.map tac_of_hint hintl
    
and e_trivial_resolve db_list local_db gl = 
  try 
    Auto.priority 
      (e_my_find_search db_list local_db 
	 (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db gl =
  try List.map snd (e_my_find_search db_list local_db 
		      (List.hd (head_constr_bound gl [])) gl)
  with Bound | Not_found -> []

let assumption_tac_list id = apply_tac_list (e_give_exact_constr (mkVar id))

let find_first_goal gls = 
  try first_goal gls with UserError _ -> assert false

(*s The following module [SearchProblem] is used to instantiate the generic
    exploration functor [Explore.Make]. *)
      
module MySearchProblem = struct

  type state = { 
    depth : int; (*r depth of search before failing *)
    tacres : goal list sigma * validation;
    last_tactic : std_ppcmds;
    dblist : Auto.hint_db list;
    localdb :  Auto.hint_db list }
		 
  let success s = (sig_it (fst s.tacres)) = []

  let rec filter_tactics (glls,v) = function
    | [] -> []
    | (tac,pptac) :: tacl -> 
	try 
	  let (lgls,ptl) = apply_tac_list tac glls in 
	  let v' p = v (ptl p) in
	  ((lgls,v'),pptac) :: filter_tactics (glls,v) tacl
	with e when Logic.catchable_exception e ->
	  filter_tactics (glls,v) tacl

  (* Ordering of states is lexicographic on depth (greatest first) then
     number of remaining goals. *)
  let compare s s' =
    let d = s'.depth - s.depth in
    let nbgoals s = List.length (sig_it (fst s.tacres)) in
    if d <> 0 then d else nbgoals s - nbgoals s'

  let branching s = 
    if s.depth = 0 then 
      []
    else      
      let lg = fst s.tacres in
      let nbgl = List.length (sig_it lg) in
      assert (nbgl > 0);
      let g = find_first_goal lg in
      let assumption_tacs = 
	let l = 
	  filter_tactics s.tacres
	    (List.map 
	       (fun id -> (e_give_exact_constr (mkVar id),
			   (str "Exact" ++ spc()++ pr_id id)))
	       (pf_ids_of_hyps g))
	in
	List.map (fun (res,pp) -> { depth = s.depth; tacres = res;
				    last_tactic = pp; dblist = s.dblist;
				    localdb = List.tl s.localdb }) l
      in
      let intro_tac = 
	List.map 
	  (fun ((lgls,_) as res,pp) -> 
	     let g' = first_goal lgls in 
	     let hintl = 
	       make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
	     in
             let ldb = add_hint_list hintl (List.hd s.localdb) in
	     { depth = s.depth; tacres = res; 
	       last_tactic = pp; dblist = s.dblist;
	       localdb = ldb :: List.tl s.localdb })
	  (filter_tactics s.tacres [Tactics.intro,(str "Intro" )])
      in
      let rec_tacs = 
	let l = 
	  filter_tactics s.tacres
	    (e_possible_resolve s.dblist (List.hd s.localdb) (pf_concl g))
	in
	List.map 
	  (fun ((lgls,_) as res, pp) -> 
	     let nbgl' = List.length (sig_it lgls) in
	     if nbgl' < nbgl then
	       { depth = s.depth; tacres = res; last_tactic = pp;
		 dblist = s.dblist; localdb = List.tl s.localdb }
	     else 
	       { depth = pred s.depth; tacres = res; 
		 dblist = s.dblist; last_tactic = pp;
		 localdb = 
		   list_addn (nbgl'-nbgl) (List.hd s.localdb) s.localdb })
	  l
      in
      List.sort compare (assumption_tacs @ intro_tac @ rec_tacs)

  let pp s = 
    msg (hov 0 (str " depth="++ int s.depth ++ spc() ++
		  s.last_tactic ++ str "\n"))

end

module MySearch = Explore.Make(MySearchProblem)

let make_initial_state n gl dblist localdb =
  { MySearchProblem.depth = n;
    MySearchProblem.tacres = tclIDTAC gl;
    MySearchProblem.last_tactic = (mt ());
    MySearchProblem.dblist = dblist;
    MySearchProblem.localdb = [localdb] }

let e_depth_search debug p db_list local_db gl =
  try
    let tac = if debug then MySearch.debug_depth_first else MySearch.depth_first in
    let s = tac (make_initial_state p gl db_list local_db) in
    s.MySearchProblem.tacres
  with Not_found -> error "EAuto: depth first search failed"

let e_breadth_search debug n db_list local_db gl =
  try
    let tac = 
      if debug then MySearch.debug_breadth_first else MySearch.breadth_first 
    in
    let s = tac (make_initial_state n gl db_list local_db) in
    s.MySearchProblem.tacres
  with Not_found -> error "EAuto: breadth first search failed"

let e_search_auto debug (n,p) db_list gl = 
  let local_db = make_local_hint_db true [] gl in 
  if n = 0 then 
    e_depth_search debug p db_list local_db gl
  else 
    e_breadth_search debug n db_list local_db gl

let eauto debug np dbnames = 
  let db_list =
    List.map
      (fun x -> 
	 try searchtable_map x
	 with Not_found -> error ("EAuto: "^x^": No such Hint database"))
      ("core"::dbnames) 
  in
  tclTRY (e_search_auto debug np db_list)

let full_eauto debug n gl = 
  let dbnames = current_db_names () in
  let dbnames =  list_subtract dbnames ["v62"] in
  let db_list = List.map searchtable_map dbnames in
  let _local_db = make_local_hint_db true [] gl in
  tclTRY (e_search_auto debug n db_list) gl

let my_full_eauto n gl = full_eauto false (n,0) gl

(**********************************************************************
   copié de tactics/auto.ml on a juste modifié search_gen
*)

(* local_db is a Hint database containing the hypotheses of current goal *)
(* Papageno : cette fonction a été pas mal simplifiée depuis que la base
  de Hint impérative a été remplacée par plusieurs bases fonctionnelles *)

let rec trivial_fail_db db_list local_db gl =
  let intro_tac = 
    tclTHEN intro 
      (fun g'->
	 let hintl = make_resolve_hyp (pf_env g') (project g') (pf_last_hyp g')
	 in trivial_fail_db db_list (add_hint_list hintl local_db) g')
  in
  tclFIRST 
    (assumption::intro_tac::
     (List.map tclCOMPLETE 
	(trivial_resolve db_list local_db (pf_concl gl)))) gl

and my_find_search db_list local_db hdc concl =
  let flags = Auto.auto_unif_flags in
  let tacl = 
    if occur_existential concl then 
      list_map_append (fun (st, db) -> List.map (fun x -> {flags with Unification.modulo_delta = st}, x) 
	(Hint_db.map_all hdc db)) (local_db::db_list)
    else 
      list_map_append (fun (st, db) -> List.map (fun x -> {flags with Unification.modulo_delta = st}, x)
	(Hint_db.map_auto (hdc,concl) db)) (local_db::db_list)
  in
  List.map 
    (fun (st, {pri=b; pat=p; code=t} as _patac) -> 
       (b,
	match t with
	  | Res_pf (term,cl)  -> unify_resolve st (term,cl)
	  | ERes_pf (_,c) -> (fun gl -> error "eres_pf")
	  | Give_exact c  -> exact_check c
	  | Res_pf_THEN_trivial_fail (term,cl) -> 
	      tclTHEN 
		(unify_resolve st (term,cl)) 
		(trivial_fail_db db_list local_db)
	  | Unfold_nth c -> unfold_in_concl [[],c]
	  | Extern tacast -> 
	      conclPattern concl (Option.get p) tacast))
    tacl

and trivial_resolve db_list local_db cl = 
  try 
    let hdconstr = List.hd (head_constr_bound cl []) in
    priority 
      (my_find_search db_list local_db (head_of_constr_reference hdconstr) cl)
  with Bound | Not_found -> 
    []

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
	   (fun id -> tclTHEN (decomp_unary_term (mkVar id)) 
		(tclTHEN 
		   (clear [id])
		   (free_try (search_gen decomp p db_list local_db []))))
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
		None
		(mkVar hid,htyp)]
	   with Failure _ -> [] 
	 in
         (free_try
	  (search_gen decomp n db_list (add_hint_list hintl local_db) [d])
	  g'))
  in
  let rec_tacs = 
    List.map 
      (fun ntac -> 
	 tclTHEN ntac
	   (free_try
	    (search_gen decomp (n-1) db_list local_db empty_named_context)))
      (possible_resolve db_list local_db (pf_concl goal))
  in 
  tclFIRST (assumption::(decomp_tacs@(intro_tac::rec_tacs))) goal


let search = search_gen 0

let default_search_depth = ref 5
			     
let full_auto n gl = 
  let dbnames = current_db_names () in
  let dbnames = list_subtract dbnames ["v62"] in
  let db_list = List.map searchtable_map dbnames in
  let hyps = pf_hyps gl in
  tclTRY (search n db_list (make_local_hint_db false [] gl) hyps) gl
  
let default_full_auto gl = full_auto !default_search_depth gl
(************************************************************************)

let blast_tactic = ref (free_try default_full_auto)
;;

let blast_auto = (free_try default_full_auto)
(*                  (tclTHEN (free_try default_full_auto)
			  (free_try (my_full_eauto 2)))
*)
;;
let blast_simpl = (free_try (reduce (Simpl None) onConcl))
;;
let blast_induction1 = 
    (free_try (tclTHEN (tclTRY intro)
		       (tclTRY (tclLAST_HYP simplest_elim))))
;;
let blast_induction2 = 
    (free_try (tclTHEN (tclTRY (tclTHEN intro intro))
		       (tclTRY (tclLAST_HYP simplest_elim))))
;;
let blast_induction3 = 
    (free_try (tclTHEN (tclTRY (tclTHEN intro (tclTHEN intro intro)))
		       (tclTRY (tclLAST_HYP simplest_elim))))
;;

blast_tactic :=
  (tclORELSE (tclCOMPLETE blast_auto)
  (tclORELSE (tclCOMPLETE (tclTHEN blast_simpl blast_auto))
  (tclORELSE (tclCOMPLETE (tclTHEN blast_induction1
                          (tclTHEN blast_simpl blast_auto)))
  (tclORELSE (tclCOMPLETE (tclTHEN blast_induction2
                          (tclTHEN blast_simpl blast_auto)))
             (tclCOMPLETE (tclTHEN blast_induction3
                          (tclTHEN blast_simpl blast_auto)))))))
;;
(*
blast_tactic := (tclTHEN (free_try default_full_auto)
			 (free_try (my_full_eauto 4)))
;;
*)

let vire_extvar s =
   let interro = ref false in
   let interro_pos = ref 0 in
   for i=0 to (length s)-1 do
     if get s i = '?'
     then (interro := true;
           interro_pos := i)
     else if (!interro && 
              (List.mem (get s i)
			['0';'1';'2';'3';'4';'5';'6';'7';'8';'9']))
     then set s i ' '
     else interro:=false
   done;
   s
;;

let blast gls =
   let leaf g = {
      open_subgoals = 1;
      goal = g;
      ref = None } in
     try (let (sgl,v) as _res = !blast_tactic gls in
	  let {it=lg} = sgl in
          if lg = [] 
          then (let pf = v (List.map leaf (sig_it sgl)) in
                let sign = (sig_it gls).evar_hyps in
                let x = print_subscript 
                     (sig_sig gls) sign pf in
		msgnl (hov 0 (str"Blast ==> " ++ x));
                let x = print_subscript 
                     (sig_sig gls) sign pf in
                let tac_string =
                pp_string  (hov 0 x ) in
    (* on remplace les ?1 ?2 ... de refine par ? *)
		parse_tac ((vire_extvar tac_string)
			   ^ ".")
	  )
	  else (msgnl (hov 0 (str"Blast failed to prove the goal..."));
		failwith "echec de blast"))
     with _ -> failwith "echec de blast"
;;

let blast_tac display_function = function 
          | (n::_) as _l -> 
                 (function g ->
                    let exp_ast = (blast g) in
                     (display_function exp_ast;
                       tclIDTAC g))
          |  _ -> failwith "expecting other arguments";;

let blast_tac_txt = 
  blast_tac
    (function x -> msgnl(Pptactic.pr_glob_tactic (Global.env()) (Tacinterp.glob_tactic x)));;

(* Obsolète ?
overwriting_add_tactic "Blast1" blast_tac_txt;;
*)

(*
Grammar tactic ne_numarg_list : list :=
  ne_numarg_single [numarg($n)] ->[$n]
| ne_numarg_cons [numarg($n) ne_numarg_list($ns)] -> [ $n ($LIST $ns) ].
Grammar tactic simple_tactic : ast :=
  blast1 [ "Blast1" ne_numarg_list($ns) ] ->
         [ (Blast1 ($LIST $ns)) ].



PATH=/usr/local/bin:/usr/bin:$PATH
COQTOP=d:/Tools/coq-7.0-3mai
CAMLLIB=/usr/local/lib/ocaml
CAMLP4LIB=/usr/local/lib/camlp4
export CAMLLIB
export COQTOP
export CAMLP4LIB 
d:/Tools/coq-7.0-3mai/bin/coqtop.byte.exe 
Drop.
#use "/cygdrive/D/Tools/coq-7.0-3mai/dev/base_include";;
*)
