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
open Identifier
open Names
open Libnames
open Prim

GEXTEND Gram
  GLOBAL: var ident metaident number string (*path*) ast astpat
  astact entry_type;

  metaident:
    [ [ s = METAIDENT -> Nmeta(loc,s) ] ]
  ;
  var:
    [ [ s = IDENT -> Nvar(loc, id_of_string s) ] ]
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
    [ [ id = IDENT; (l,a) = astfields -> 
          Path(loc, make_path (make_dirpath (id_of_string id :: l)) a CCI)
      | id = IDENT -> Nvar(loc, id_of_string id)
      ] ]
  ;
  astfields:
    [ [ id = FIELD; (l,a) = astfields -> id_of_string id :: l, a
      | id = FIELD -> [], id_of_string id
      ] ]
  ;
  astident:
    [ [ s = IDENT -> s ] ]
  ;
  (* ast *)
  ast:
    [ [ id = metaident -> id
      | p = astpath -> p
      | s = INT -> Num(loc, int_of_string s)
      | s = STRING -> Str(loc, s)
      | "{"; s = METAIDENT; "}" -> Id(loc,s)
      | "("; nname = astident; l = LIST0 ast; ")" -> Node(loc,nname,l)
      | "("; METAIDENT "$LIST"; id = metaident; ")" -> Node(loc,"$LIST",[id])
      | "("; METAIDENT "$STR"; id = metaident; ")" -> Node(loc,"$STR",[id])
      | "("; METAIDENT "$VAR"; id = metaident; ")" -> Node(loc,"$VAR",[id])
      | "("; METAIDENT "$ID"; id = metaident; ")" -> Node(loc,"$ID",[id])
      | "("; METAIDENT "$ABSTRACT"; l = LIST0 ast;")"->Node(loc,"$ABSTRACT",l)
      | "("; METAIDENT "$PATH"; id = metaident; ")" -> Node(loc,"$PATH",[id])
      | "("; METAIDENT "$NUM"; id = metaident; ")" -> Node(loc,"$NUM",[id])
      | "["; "<>"; "]"; b = ast -> Slam(loc,None,b)
      | "["; a = ast; "]"; b = ast ->
	  (match a with
	    | Nvar (_,id) -> Slam(loc,Some id,b)
	    | Nmeta (_,s) -> Smetalam(loc,s,b)
	    | _ -> failwith "Slam expects a var or a metavar")

(*
      | "["; ido = astidoption; "]"; b = ast -> Slam(loc,ido,b)
      | "["; id = METAIDENT; "]"; b = ast -> Smetalam(loc,id,b)
*)
      | "'"; a = ast -> Node(loc,"$QUOTE",[a]) ] ]
  ;
(*
  astidoption:
    [ [ "<>" -> None
      | id = IDENT -> Some (id_of_string id) ] ]
  ;
*)
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
