(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Coqast
open Pcoq
open Names
open Libnames
open Topconstr
open Prim

let _ = reset_all_grammars()

open Nametab
let local_id_of_string = id_of_string
let local_make_dirpath = make_dirpath
let local_make_qualid l id' = make_qualid (local_make_dirpath l) id'
let local_make_short_qualid id = make_short_qualid id
let local_make_posint = int_of_string
let local_make_negint n = - int_of_string n
let local_make_path l a = encode_kn (local_make_dirpath l) a
let local_make_binding loc a b =
  match a with
    | Nvar (_,id) -> Slam(loc,Some id,b)
    | Nmeta (_,s) -> Smetalam(loc,s,b)
    | _ -> failwith "Slam expects a var or a metavar"
let local_append l id = l@[id]

GEXTEND Gram
  GLOBAL: ident natural integer bigint string preident ast
    astlist qualid reference dirpath identref name base_ident var hyp;

 (* Compatibility: Prim.var is a synonym of Prim.ident *)
  var:
    [ [ id = ident -> id ] ]
  ;
  hyp:
    [ [ id = ident -> id ] ]
  ;
  metaident:
    [ [ s = METAIDENT -> Nmeta (loc,s) ] ]
  ;
  preident:
    [ [ s = IDENT -> s ] ]
  ;
  base_ident:
    [ [ s = IDENT -> local_id_of_string s ] ]
  ;
  name:
    [ [ IDENT "_" -> (loc, Anonymous)
      | id = base_ident -> (loc, Name id) ] ]
  ;
  identref:
    [ [ id = base_ident -> (loc,id) ] ]
  ;
  ident:
    [ [ id = base_ident -> id ] ]
  ;
  natural:
    [ [ i = INT -> local_make_posint i ] ]
  ;
  bigint:
    [ [ i = INT -> Bignat.POS (Bignat.of_string i)
      | "-"; i = INT -> Bignat.NEG (Bignat.of_string i) ] ]
  ;
  integer:
    [ [ i = INT      -> local_make_posint i
      | "-"; i = INT -> local_make_negint i ] ]
  ;
  field:
    [ [ s = FIELD -> local_id_of_string s ] ]
  ;
  dirpath:
    [ [ id = base_ident; l = LIST0 field ->
        local_make_dirpath (local_append l id) ] ]
  ;
  fields:
    [ [ id = field; (l,id') = fields -> (local_append l id,id')
      | id = field -> ([],id)
      ] ]
  ;
  basequalid:
    [ [ id = base_ident; (l,id')=fields -> local_make_qualid (local_append l id) id'
      | id = base_ident -> local_make_short_qualid id
      ] ]
  ;
  qualid:
    [ [ qid = basequalid -> loc, qid ] ]
  ;
  reference:
    [ [ id = base_ident; (l,id') = fields ->
        Qualid (loc, local_make_qualid (local_append l id) id')
      | id = base_ident -> Ident (loc,id)
      ] ]
  ;
  string:
    [ [ s = STRING -> s ] ]
  ;
  astpath:
    [ [ id = base_ident; (l,a) = fields ->
          Path(loc, local_make_path (local_append l id) a)
      | id = base_ident -> Nvar(loc, id)
      ] ]
  ;
  (* ast *)
  ast:
    [ [ id = metaident -> id
      | p = astpath -> p
      | s = INT -> Num(loc, local_make_posint s)
      | s = STRING -> Str(loc, s)
      | "{"; s = METAIDENT; "}" -> Id(loc,s)
      | "("; nname = IDENT; l = LIST0 ast; ")" -> Node(loc,nname,l)
      | "("; METAIDENT "$LIST"; id = metaident; ")" -> Node(loc,"$LIST",[id])
      | "("; METAIDENT "$STR"; id = metaident; ")" -> Node(loc,"$STR",[id])
      | "("; METAIDENT "$VAR"; id = metaident; ")" -> Node(loc,"$VAR",[id])
      | "("; METAIDENT "$ID"; id = metaident; ")" -> Node(loc,"$ID",[id])
      | "("; METAIDENT "$ABSTRACT"; l = LIST0 ast;")"->Node(loc,"$ABSTRACT",l)
      | "("; METAIDENT "$PATH"; id = metaident; ")" -> Node(loc,"$PATH",[id])
      | "("; METAIDENT "$NUM"; id = metaident; ")" -> Node(loc,"$NUM",[id])
      | "["; "<>"; "]"; b = ast -> Slam(loc,None,b)
      | "["; a = ast; "]"; b = ast -> local_make_binding loc a b

(*
      | "["; ido = astidoption; "]"; b = ast -> Slam(loc,ido,b)
      | "["; id = METAIDENT; "]"; b = ast -> Smetalam(loc,id,b)
*)
      | "'"; a = ast -> Node(loc,"$QUOTE",[a]) ] ]
  ;
  astlist:
    [ [ l = LIST0 ast -> l ] ]
  ;
END
