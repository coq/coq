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
open Module
open Util

(* Grammar rules for module expressions and types *)

GEXTEND Gram
  GLOBAL: identarg qualidarg ne_binders_list module_expr 
          module_type;
 
  identarg:
    [ [ id = Constr.ident -> id ] ]
  ;
  qualidarg:
    [ [ l = Constr.qualid -> l ] ]
  ;
  
  ident_comma_list_tail:
    [ [ ","; idl = LIST0 identarg SEP "," -> idl
      | -> [] ] ]
  ;

  vardecls: (* This is interpreted by Pcoq.abstract_binder *)
    [ [ id = identarg; idl = ident_comma_list_tail; 
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
    [ [ qid = qualidarg -> <:ast< (MODEXPRQID ($LIST $qid)) >>
      | me1 = module_expr; me2 = module_expr -> 
	  <:ast< (MODEXPRAPP $me1 $me2) >>
      | "("; me = module_expr; ")" ->
	  me
(* ... *)
      ] ]
  ;

  module_type:
    [ [ qid = qualidarg -> <:ast< (MODTQUALID ($LIST $qid)) >>
(* ... *)
      ] ]
  ;
END
