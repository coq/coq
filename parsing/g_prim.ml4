
(* $Id$ *)

open Coqast
open Pcoq

open Prim

GEXTEND Gram
  GLOBAL: var ident number string path ast astpat astact entry_type;

  var:
    [ [ s = LIDENT -> Nvar(loc,s) ] ]
  ;
  ident:
    [ [ s = LIDENT -> Id(loc,s) ] ]
  ;
  number:
    [ [ i = INT -> Num(loc, int_of_string i) ] ]
  ;
  string:
    [ [ s = STRING -> Str(loc,s) ] ]
  ;
  path:
    [ [ (l,pk) = qualid -> Path(loc,l,pk) ] ]
  ;
  qualid:
    [ [ "#"; l = LIST1 LIDENT SEP "#"; "."; pk = LIDENT -> (l, pk) ] ]
  ;

  (* ast *)
  ast:
    [ [ id = LIDENT -> Nvar(loc,id)
      | s = INT -> Num(loc, int_of_string s)
      | s = STRING -> Str(loc,s)
      | p = path -> p
      | "{"; s = LIDENT; "}" -> Id(loc,s)
      | "("; nname = LIDENT; l = LIST0 ast; ")" -> Node(loc,nname,l)
      | "["; ido = idoption; "]"; b = ast -> Slam(loc,ido,b)
      | "'"; a = ast -> Node(loc,"$QUOTE",[a]) ] ]
  ;
  idoption:
    [ [ "<>" -> None
      | id = LIDENT -> Some id ] ]
  ;

  (* meta-syntax entries *)
  astpat:
    [ [ a = ast -> Node loc "ASTPAT" [a] ] ]
  ; 
  astact:
    [ [ a = action -> Node loc "ASTACT" [a] ] ]
  ;
  astlist:
    [ [ l = LIST0 ast -> Node loc "ASTLIST" l ] ]
  ;
  action:
    [ [ LIDENT "let"; p = astlist; et = entry_type; "="; e1 = action; "in";
        e = action -> Node(loc,"$CASE",[e1; et; Node(loc,"CASE",[p;e])])
      | LIDENT "case"; a = action; et = entry_type; "of";
        cl = LIST1 case SEP "|"; LIDENT "esac" ->
          Node(loc,"$CASE",a::et::cl)
      | "["; al = astlist; "]" -> al ] ]
  ;
  case:
    [[ p = astlist; "->"; a = action -> Node(loc,"CASE",[p;a]) ]]
  ;
  entry_type:
    [[ ":"; LIDENT "List" -> Id(loc,"LIST")
     | ":"; LIDENT "Ast" -> Id(loc,"AST")
     | -> Id(loc,"AST") ]]
  ;
END
