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

open Indfun_common
open Pp
open Libnames
open Names
open Term


open Pcoq

open Genarg
open Vernac_
open Prim
open Constr
open G_constr
open G_vernac
open Indfun
open Topconstr

open Tacinterp;;

let _ = ref 0;;


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
	       ( id_of_string ((string_of_id fname)^"_2"))
	       (Tacticals.elimination_sort_of_goal g)
	   )
       in
       let princ = 
	 let _,princ_ref = 
	   qualid_of_reference (Libnames.Ident (Util.dummy_loc,princ_name))
	 in
	 try Nametab.locate_constant princ_ref
	 with Not_found -> Util.error "Don't know the induction scheme to use"
       in
       
       Tacticals.tclTHEN 
	 (Hiddentac.h_reduce 
	    (Rawterm.Pattern (List.map (fun e -> ([],e)) (args@[c])))
	    Tacticals.onConcl
	 )
	 ((Hiddentac.h_apply (mkConst princ,Rawterm.NoBindings)))
	 g
     ]
END

VERNAC ARGUMENT EXTEND rec_annotation2
  [ "{"  "struct" ident(id)  "}"] -> [ id ]
END


VERNAC ARGUMENT EXTEND binder2
    [ "(" ne_ident_list(idl) ":" lconstr(c)  ")"] ->
     [
       LocalRawAssum (List.map (fun id -> (Util.dummy_loc,Name id)) idl,c) ]
END


VERNAC ARGUMENT EXTEND rec_definition2
 [ ident(id)  binder2_list( bl)
     rec_annotation2_opt(annot) ":" constr( type_)
	":=" lconstr(def)] ->
          [let names = List.map snd (Topconstr.names_of_local_assums bl) in
	   let check_one_name () =
	     if List.length names > 1 then
               Util.user_err_loc
                 (Util.dummy_loc,"GenFixpoint",
                  Pp.str "the recursive argument needs to be specified");
	   in
	   let check_exists_args id =
	     (try ignore(Util.list_index (Name id) names - 1); annot
	      with Not_found ->  Util.user_err_loc
                (Util.dummy_loc,"GenFixpoint",
                 Pp.str "No argument named " ++ Nameops.pr_id id)
	     )
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

