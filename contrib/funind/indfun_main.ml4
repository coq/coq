(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(**************************************************************************)
(*                                                                        *)
(* function induction / functional inversion / new version                *)
(*                                                                        *)
(* Julien Forest (INRIA Sophia-Antipolis, France)                         *)
(*                                                                        *)
(**************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* open Indfun_common *)
(* open Pp *)
(* open Libnames *)
(* open Names *)
(* open Term *)


(* open Pcoq *)

(* open Genarg *)
(* open Vernac_ *)
(* open Prim *)
(* open Constr *)
(* open G_constr *)
(* open G_vernac *)
(* open Indfun *)
(* open Topconstr *)

(* open Tacinterp *)
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
       let princ_info = 
	 let princ_type = 
	(try (match (Global.lookup_constant princ) with
		  {Declarations.const_type=t} -> t
	     )
	 with _ -> assert false)
	 in
	 Tactics.compute_elim_sig (mkRel 0,Rawterm.NoBindings) princ_type
       in
(* 	   msg *)
(* 	     (str "computing non parameters argument for " ++ *)
(* 		Ppconstr.pr_id princ_name ++ fnl () ++ *)
(* 		str "detected params are : " ++ *)
(* 		Util.prlist_with_sep spc (fun (id,_,_) -> Ppconstr.pr_name id) princ_info.Tactics.params ++ fnl ()++ *)
(* 		str  "detected arguments are " ++ *)
(* 		Util.prlist_with_sep spc (Printer.pr_lconstr_env (Tacmach.pf_env g))  args ++ fnl ()  *)
(* 	      ++ str " number of predicates " ++ *)
(* 		str (string_of_int (List.length princ_info.Tactics.predicates))++ fnl () ++ *)
(* 		str " number of branches " ++ *)
(* 		str (string_of_int (List.length princ_info.Tactics.branches)) *)
(* 	     ); *)

       let frealargs = 
	 try
	   snd (Util.list_chop (List.length princ_info.Tactics.params) args)
	 with _ -> 
	   msg_warning
	     (str "computing non parameters argument for " ++
		Ppconstr.pr_id princ_name ++ fnl () ++
		str " detected params number is : " ++
		str (string_of_int (List.length princ_info.Tactics.params)) ++ fnl ()++
		str  " while number of arguments is " ++
		str (string_of_int (List.length args)) ++ fnl () 
(* 		str " number of predicates " ++  *)
(* 		str (string_of_int (List.length princ_info.predicates))++ fnl () ++ *)
(* 		str " number of branches " ++  *)
(* 		str (string_of_int (List.length princ_info.branches)) *)
	     );args
	     
       in
       Tacticals.tclTHEN 
	 (Hiddentac.h_reduce 
	    (Rawterm.Pattern (List.map (fun e -> ([],e)) (frealargs@[c])))
	    Tacticals.onConcl
	 )
	 (Hiddentac.h_apply (mkConst princ,Rawterm.NoBindings))
     	 g
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
		  check_one_name ();
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
	[ do_generate_principle recsl]
      END
