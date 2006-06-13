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
       functional_induction true c princl pat ]
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
