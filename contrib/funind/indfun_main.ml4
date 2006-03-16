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

TACTIC EXTEND newfuninv
   [ "functional" "inversion" ident(hyp) ident(fname) ] -> 
     [
       Invfun.invfun hyp fname
     ]
END



TACTIC EXTEND newfunind
   ["new" "functional" "induction" constr(c) ] -> 
     [
       let f,args = decompose_app c in 
       let fname = 
	 match kind_of_term f with 
	   | Const c' -> 
	       id_of_label (con_label c') 
	   | _ -> Util.error "Must be used with a function" 
       in
       fun g -> 
       let princ_name = 
	   (
	     Indrec.make_elimination_ident
	       fname
	       (Tacticals.elimination_sort_of_goal g)
	   )
       in
       let princ = const_of_id princ_name in
       let args_as_induction_constr =
	 List.map (fun c -> Tacexpr.ElimOnConstr c) (args@[c]) 
       in 
       let princ' = Some (mkConst princ,Rawterm.NoBindings) in 
       Tactics.new_induct args_as_induction_constr princ' Genarg.IntroAnonymous g
     ]
END

VERNAC ARGUMENT EXTEND rec_annotation2
  [ "{"  "struct" ident(id)  "}"] -> [ Struct id ]
| [ "{" "wf" constr(r) ident_opt(id) "}" ] -> [ Wf(r,id) ]
| [ "{" "mes" constr(r) ident_opt(id) "}" ] -> [ Mes(r,id) ] 
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
           (Util.dummy_loc,"GenFixpoint",
            Pp.str "the recursive argument needs to be specified");
     in
     let check_exists_args an =
       try 
	 let id = match an with Struct id -> id | Wf(_,Some id) -> id | Mes(_,Some id) -> id | Wf(_,None) | Mes(_,None) -> failwith "check_exists_args" in 
	 (try ignore(Util.list_index (Name id) names - 1); annot
	  with Not_found ->  Util.user_err_loc
            (Util.dummy_loc,"GenFixpoint",
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


VERNAC COMMAND EXTEND GenFixpoint
   ["GenFixpoint" rec_definitions2(recsl)] ->
	[ do_generate_principle false  recsl]
END

VERNAC COMMAND EXTEND IGenFixpoint
   ["IGenFixpoint" rec_definitions2(recsl)] ->
	[ do_generate_principle true  recsl]
END

VERNAC COMMAND EXTEND NewFunctionalScheme
   ["New" "Functional" "Scheme" ident(name) ident_list(funs)  "using" ident(scheme)] ->
    [
      let id_to_constr id = 
	Tacinterp.constr_of_id (Global.env ())  id
      in 
      let funs =
	Array.of_list (List.map id_to_constr funs) 
      in 
      let scheme = id_to_constr scheme in 
      let scheme_type = Typing.type_of (Global.env ()) Evd.empty scheme in 
      New_arg_principle.generate_functional_principle false 
	scheme_type 
	(Some name) 
	(Array.map destConst funs)
	0
	(New_arg_principle.prove_princ_for_struct false 0 (Array.map destConst funs))
    ]
END

