(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *) 

open Pp
open Ast
open Pcoq
open Prim
open Module
open Util

(* Grammar rules for module expressions and types *)

GEXTEND Gram
  GLOBAL: ne_binders_list module_expr 
          module_type;
 
  ident:
    [ [ id = Prim.var -> id ] ]
  ;

  ident_comma_list_tail:
    [ [ ","; idl = LIST0 ident SEP "," -> idl
      | -> [] ] ]
  ;

  qualid:
    [ [ id = Prim.var; l = fields -> <:ast< (QUALID $id ($LIST $l)) >>
      | id = Prim.var -> <:ast< (QUALID $id) >>
      ] ]
  ;
  fields:
    [ [ id = FIELD; l = fields -> <:ast< ($VAR $id) >> :: l
      | id = FIELD -> [ <:ast< ($VAR $id) >> ]
      ] ]
  ;

  vardecls: (* This is interpreted by Pcoq.abstract_binder *)
    [ [ id = ident; idl = ident_comma_list_tail; 
	":"; mty = module_type ->
          <:ast< (BINDER $mty $id ($LIST $idl)) >> ] ]
  ;

  ne_vardecls_list:
    [ [ id = vardecls; ";"; idl = ne_vardecls_list -> id :: idl
      | id = vardecls -> [id] ] ]
  ;
  
  rawbinders:
    [ [ "["; bl = ne_vardecls_list; "]" -> bl ] ]
  ;

  ne_binders_list:
    [ [ bl = rawbinders; bll = ne_binders_list -> bl @ bll
      | bl = rawbinders -> bl ] ]
  ;

  module_expr:
    [ [ qid = qualid -> <:ast< (MODEXPRQID $qid) >>
      | me1 = module_expr; me2 = module_expr -> 
	  <:ast< (MODEXPRAPP $me1 $me2) >>
      | "("; me = module_expr; ")" ->
	  me
(* ... *)
      ] ]
  ;

  with_declaration:
    [ [ "Definition"; id = ident; ":="; c = Constr.constr ->
	  <:ast< (WITHDEFINITION $id $c) >>
      | IDENT "Module"; id = ident; ":="; qid = qualid ->
	  <:ast< (WITHMODULE $id $qid) >>
      ] ]
  ;
  
  module_type:
    [ [ qid = qualid -> <:ast< (MODTYPEQID $qid) >>
(* ... *)
      | mty = module_type; "with"; decl = with_declaration -> 
	  <:ast< (MODTYPEWITH $mty $decl)>> ] ]
  ;
END
