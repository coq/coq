(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *) 

open Pp
open Ast
open Pcoq
open Prim
open Module
open Util
open Topconstr

(* Grammar rules for module expressions and types *)

if !Options.v7 then
GEXTEND Gram
  GLOBAL: module_expr module_type;
 
  module_expr:
    [ [ qid = qualid -> CMEident qid
      | me1 = module_expr; me2 = module_expr -> CMEapply (me1,me2)
      | "("; me = module_expr; ")" -> me
(* ... *)
      ] ]
  ;

  with_declaration:
    [ [ "Definition"; id = identref; ":="; c = Constr.constr ->
          CWith_Definition (id,c)
      | IDENT "Module"; id = identref; ":="; qid = qualid ->
	  CWith_Module (id,qid)
      ] ]
  ;
  
  module_type:
    [ [ qid = qualid -> CMTEident qid
(* ... *)
      | mty = module_type; "with"; decl = with_declaration -> 
	  CMTEwith (mty,decl) ] ]
  ;
END
