(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Coqast
open Pcoq

open Prim

GEXTEND Gram
  GLOBAL: var ident metaident number string path ast astpat astact entry_type;

  var:
    [ [ s = IDENT -> Nvar(loc,s) ] ]
  ;
  metaident:
    [ [ s = METAIDENT -> Nvar(loc,s) ] ]
  ;
  ident:
    [ [ s = IDENT -> Id(loc,s) ] ]
  ;
  number:
    [ [ i = INT -> Num(loc, int_of_string i) ] ]
  ;
  string:
    [ [ s = STRING -> Str(loc,s) ] ]
  ;
  astpath:
    [ [ (l,pk) = astqualid -> Path(loc,l,pk) ] ]
  ;
  astqualid:
    [ [ "#"; l = LIST1 IDENT SEP "#"; "."; pk = IDENT -> (l, pk) ] ]
  ;
  astident:
    [ [ s = IDENT -> s 
      | s = METAIDENT -> s ] ]
  ;
  (* ast *)
  ast:
    [ [ id = astident -> Nvar(loc,id)
      | s = INT -> Num(loc, int_of_string s)
      | s = STRING -> Str(loc,s)
      | p = astpath -> p
      | "{"; s = IDENT; "}" -> Id(loc,s)
      | "("; nname = astident; l = LIST0 ast; ")" -> Node(loc,nname,l)
      | "["; ido = astidoption; "]"; b = ast -> Slam(loc,ido,b)
      | "'"; a = ast -> Node(loc,"$QUOTE",[a]) ] ]
  ;
  astidoption:
    [ [ "<>" -> None
      | id = astident -> Some id ] ]
  ;

  (* meta-syntax entries *)
  astpat:
    [ [ "<<" ; a = ast; ">>" -> Node loc "ASTPAT" [a]
      | a = default_action_parser -> Node loc "ASTPAT" [a] ] ]
  ; 
  astact:
    [ [ a = action -> Node loc "ASTACT" [a] ] ]
  ;
  astlist:
    [ [ l = LIST0 ast -> Node loc "ASTLIST" l ] ]
  ;
  action:
    [ [ IDENT "let"; p = astlist; et = entry_type; "="; e1 = action; "in";
        e = action -> Node(loc,"$CASE",[e1; et; Node(loc,"CASE",[p;e])])
      | IDENT "case"; a = action; et = entry_type; "of";
        cl = LIST1 case SEP "|"; IDENT "esac" ->
          Node(loc,"$CASE",a::et::cl)
      | "["; al = default_action_parser; "]" -> al ] ]
  ;
  case:
    [[ p = astlist; "->"; a = action -> Node(loc,"CASE",[p;a]) ]]
  ;
  entry_type:
    [[ ":"; IDENT "ast"; IDENT "list" -> 
	 let _ = set_default_action_parser astlist in Id(loc,"LIST")
     | ":"; IDENT "List" -> (* For compatibility *)
	 let _ = set_default_action_parser astlist in Id(loc,"LIST")
     | ":"; IDENT "list" -> (* For compatibility *)
	 let _ = set_default_action_parser astlist in Id(loc,"LIST")
     | ":"; IDENT "ast" ->
	 let _ = set_default_action_parser ast in Id(loc,"AST")
     | ":"; IDENT "constr" ->
	 let _ = set_default_action_parser Constr.constr in Id(loc,"AST")
     | ":"; IDENT "tactic" ->
	 let _ = set_default_action_parser Tactic.tactic in Id(loc,"AST")
     | ":"; IDENT "vernac" ->
	 let _ = set_default_action_parser Vernac_.vernac in Id(loc,"AST")
     | -> Id(loc,"AST") ]]
  ;
END
