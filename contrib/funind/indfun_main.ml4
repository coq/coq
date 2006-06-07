(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i camlp4deps: "parsing/grammar.cma" i*)
open Term
open Names
open Pp
open Topconstr
open Indfun_common 
open Indfun
open Genarg
open Pcoq

let pr_binding prc = function
  | loc, Rawterm.NamedHyp id, c -> hov 1 (Ppconstr.pr_id id ++ str " := " ++ cut () ++ prc c)
  | loc, Rawterm.AnonHyp n, c -> hov 1 (int n ++ str " := " ++ cut () ++ prc c)

let pr_bindings prc prlc = function
  | Rawterm.ImplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++
      Util.prlist_with_sep spc prc l
  | Rawterm.ExplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++ 
        Util.prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | Rawterm.NoBindings -> mt ()


let pr_with_bindings prc prlc (c,bl) =
  prc c ++ hv 0 (pr_bindings prc prlc bl)


let pr_fun_ind_using  prc prlc _ opt_c = 
  match opt_c with
    | None -> mt ()
    | Some c -> spc () ++ hov 2 (str "using" ++ spc () ++ pr_with_bindings prc prlc c)

ARGUMENT EXTEND fun_ind_using
  TYPED AS constr_with_bindings_opt
  PRINTED BY pr_fun_ind_using
| [ "using" constr_with_bindings(c) ] -> [ Some c ]
| [ ] -> [ None ]
END


TACTIC EXTEND newfuninv
   [ "functional" "inversion" ident(hyp) ident(fname) fun_ind_using(princl)] -> 
     [
       fun g -> 
	 let fconst = const_of_id fname in
	 let princ = 
	   match princl with 
	     | None -> 
		 let f_ind_id =  
		   (
		     Indrec.make_elimination_ident
		       fname 
		       (Tacticals.elimination_sort_of_goal g)
		   )
	       in
		 let princ = const_of_id f_ind_id in
		 princ
	     | Some princ -> destConst (fst princ)
	 in       
	 Invfun.invfun hyp fconst princ g
     ]
END


let pr_intro_as_pat prc _ _ pat = 
  match pat with 
    | Some pat -> spc () ++ str "as" ++ spc () ++ pr_intro_pattern pat
    | None -> mt ()


ARGUMENT EXTEND with_names TYPED AS intro_pattern_opt PRINTED BY pr_intro_as_pat
|   [ "as"  simple_intropattern(ipat) ] -> [ Some ipat ] 
| []  ->[ None ] 
END


let is_rec scheme_info = 
  let test_branche min acc (_,_,br) = 
    acc ||
      (let new_branche = Sign.it_mkProd_or_LetIn mkProp (fst (Sign.decompose_prod_assum br)) in 
      let free_rels_in_br = Termops.free_rels new_branche in 
      let max = min + scheme_info.Tactics.npredicates in 
      Util.Intset.exists (fun i -> i >= min && i< max) free_rels_in_br)
  in
  Util.list_fold_left_i test_branche 1 false (List.rev scheme_info.Tactics.branches)


let choose_dest_or_ind scheme_info =
    if is_rec scheme_info
    then Tactics.new_induct
    else Tactics.new_destruct


TACTIC EXTEND newfunind
   ["functional" "induction" ne_constr_list(cl) fun_ind_using(princl) with_names(pat)] -> 
     [
       let pat = 
	 match pat with 
	   | None -> IntroAnonymous
	   | Some pat -> pat
       in
       let c = match cl with 
	 | [] -> assert false
	 | [c] -> c 
	 | c::cl -> applist(c,cl)
       in 
       let f,args = decompose_app c in 
       fun g -> 
	 let princ,bindings = 
	   match princl with 
	     | None -> (* No principle is given let's find the good one *)
		 let fname = 
		   match kind_of_term f with 
		     | Const c' -> 
			 id_of_label (con_label c') 
		     | _ -> Util.error "Must be used with a function" 
		 in
		 let princ_name = 
		   (
		     Indrec.make_elimination_ident
		       fname
		       (Tacticals.elimination_sort_of_goal g)
		   )
		 in
		 mkConst(const_of_id princ_name ),Rawterm.NoBindings
	     | Some princ -> princ 
	 in
	 let princ_type = Tacmach.pf_type_of g princ in 
	 let princ_infos = Tactics.compute_elim_sig princ_type in 
	 let args_as_induction_constr =
	   let c_list = 
	     if princ_infos.Tactics.farg_in_concl 
	     then [c] else [] 
	   in
	   List.map (fun c -> Tacexpr.ElimOnConstr c) (args@c_list) 
	 in 
	 let princ' = Some (princ,bindings) in 
	 let princ_vars = 
	   List.fold_right 
	     (fun a acc -> 
		try Idset.add (destVar a) acc
		with _ -> acc
	     )
	     args
	     Idset.empty
	 in
	 let old_idl = List.fold_right Idset.add (Tacmach.pf_ids_of_hyps g) Idset.empty in 
	 let old_idl = Idset.diff old_idl princ_vars in 
	 let subst_and_reduce g = 
	   let idl = 
	     Util.map_succeed 
	       (fun id -> 
		  if Idset.mem id old_idl then failwith "";
		  id 
	       )
	       (Tacmach.pf_ids_of_hyps g)
	   in 
	   let flag = 
	     Rawterm.Cbv
	       {Rawterm.all_flags 
		with Rawterm.rDelta = false; 		 
	       }
	   in
	   Tacticals.tclTHEN
	     (Tacticals.tclMAP (fun id -> Tacticals.tclTRY (Equality.subst [id])) idl )
	     (Hiddentac.h_reduce flag Tacticals.allClauses)
	     g
	 in
	 Tacticals.tclTHEN
	   (choose_dest_or_ind 
	   princ_infos
	   args_as_induction_constr
	   princ'
	   pat)
	   subst_and_reduce
	   g
     ]
END


VERNAC ARGUMENT EXTEND rec_annotation2
  [ "{"  "struct" ident(id)  "}"] -> [ Struct id ]
| [ "{" "wf" constr(r) ident_opt(id) "}" ] -> [ Wf(r,id) ]
| [ "{" "measure" constr(r) ident_opt(id) "}" ] -> [ Mes(r,id) ] 
END


VERNAC ARGUMENT EXTEND binder2
    [ "(" ne_ident_list(idl) ":" lconstr(c)  ")"] ->
     [
       LocalRawAssum (List.map (fun id -> (Util.dummy_loc,Name id)) idl,c) ]
END


VERNAC ARGUMENT EXTEND rec_definition2
 [ ident(id)  binder2_list( bl)
     rec_annotation2_opt(annot) ":" lconstr( type_)
	":=" lconstr(def)] ->
    [let names = List.map snd (Topconstr.names_of_local_assums bl) in
     let check_one_name () =
       if List.length names > 1 then
         Util.user_err_loc
           (Util.dummy_loc,"Function",
            Pp.str "the recursive argument needs to be specified");
     in
     let check_exists_args an =
       try 
	 let id = match an with Struct id -> id | Wf(_,Some id) -> id | Mes(_,Some id) -> id | Wf(_,None) | Mes(_,None) -> failwith "check_exists_args" in 
	 (try ignore(Util.list_index (Name id) names - 1); annot
	  with Not_found ->  Util.user_err_loc
            (Util.dummy_loc,"Function",
             Pp.str "No argument named " ++ Nameops.pr_id id)
	 )
       with Failure "check_exists_args" ->  check_one_name ();annot
     in
     let ni =
       match annot with
         | None ->
             annot
	 | Some an ->
	     check_exists_args an
     in
     (id, ni, bl, type_, def) ]
      END


VERNAC ARGUMENT EXTEND rec_definitions2
| [ rec_definition2(rd) ] -> [ [rd] ]
| [ rec_definition2(hd) "with" rec_definitions2(tl) ] -> [ hd::tl ]
END


VERNAC COMMAND EXTEND Function
   ["Function" rec_definitions2(recsl)] ->
	[ do_generate_principle false  recsl]
END


VERNAC ARGUMENT EXTEND fun_scheme_arg
| [ ident(princ_name) ":=" "Induction" "for" ident(fun_name) "Sort" sort(s) ] -> [ (princ_name,fun_name,s) ] 
END 

VERNAC ARGUMENT EXTEND fun_scheme_args
| [ fun_scheme_arg(fa) ] -> [ [fa] ] 
| [ fun_scheme_arg(fa) "with" fun_scheme_args(fas) ] -> [fa::fas]
END 

VERNAC COMMAND EXTEND NewFunctionalScheme
   ["Functional" "Scheme" fun_scheme_args(fas) ] ->
    [
      try 
	Functional_principles_types.make_scheme fas
      with Functional_principles_types.No_graph_found -> 
	match fas with 
	  | (_,fun_name,_)::_ -> 
	      begin
		make_graph fun_name;
		try Functional_principles_types.make_scheme fas
		with Functional_principles_types.No_graph_found -> 
		  Util.error ("Cannot generate induction principle(s)")
	      end
	  | _ -> assert false (* we can only have non empty  list *)
    ]
END


VERNAC COMMAND EXTEND NewFunctionalCase
   ["Functional" "Case" fun_scheme_arg(fas) ] ->
    [
      Functional_principles_types.make_case_scheme fas
    ]
END


VERNAC COMMAND EXTEND GenerateGraph 
["Generate" "graph" "for" ident(c)] -> [ make_graph c ]
END
