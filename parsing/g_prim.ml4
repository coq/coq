(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*
camlp4o pa_ifdef.cmo pa_extend.cmo pr_o.cmo pr_extend.cmo -quotify -DQuotify -impl parsing/g_prim.ml4
*)

open Coqast
open Pcoq
open Names

ifdef Quotify then
open Qast

open Prim

(* camlp4o pa_extend.cmo pa_extend_m.cmo pr_o.cmo q_prim.ml *)

ifdef Quotify then
module Prelude = struct
let local_id_of_string s = Apply ("Names","id_of_string", [s])
let local_make_dirpath l = Qast.Apply ("Nametab","make_dirpath",[l])
let local_make_posint s = s
let local_make_negint s = Apply ("Pervasives","~-", [s])
let local_make_qualid l id' = 
  Qast.Apply ("Nametab","make_qualid", [local_make_dirpath l;id'])
let local_make_short_qualid id =
  Qast.Apply ("Nametab","make_short_qualid",[id])
let local_make_path l id' =
  Qast.Apply ("Names","make_path", [local_make_dirpath l;id'])
let local_make_binding loc a b =
  match a with
    | Qast.Node ("Nvar", [_;id]) ->
	Qast.Node ("Slam", [Qast.Loc; Qast.Option (Some id); b])
    | Qast.Node ("Nmeta", [_;s]) ->
	Qast.Node ("Smetalam", [Qast.Loc;s;b])
    | _ -> 
	Qast.Apply ("Pervasives", "failwith", [Qast.Str "Slam expects a var or a metavar"])
let local_append l id = Qast.Apply ("List","append", [l; Qast.List [id]])
end

else

module Prelude = struct
open Nametab
let local_id_of_string = id_of_string
let local_make_dirpath = make_dirpath
let local_make_qualid l id' = make_qualid (local_make_dirpath l) id'
let local_make_short_qualid id = make_short_qualid id
let local_make_posint = int_of_string
let local_make_negint n = - int_of_string n
let local_make_path l a = make_path (local_make_dirpath l) a
let local_make_binding loc a b =
  match a with
    | Nvar (_,id) -> Slam(loc,Some id,b)
    | Nmeta (_,s) -> Smetalam(loc,s,b)
    | _ -> failwith "Slam expects a var or a metavar"
let local_append l id = l@[id]
end

open Prelude

ifdef Quotify then
open Q

GEXTEND Gram
  GLOBAL: var ident natural metaident integer string preident ast astpat
  astact astlist qualid reference dirpath rawident numarg;

  metaident:
    [ [ s = METAIDENT -> Nmeta (loc,s) ] ]
  ;
  var:
    [ [ id = ident -> Nvar(loc, id) ] ]
  ;
  preident:
    [ [ s = IDENT -> s ] ]
  ;
  ident:
    [ [ s = IDENT -> local_id_of_string s ] ]
  ;
  rawident:
    [ [ id = ident -> (loc,id) ] ]
  ;
  natural:
    [ [ i = INT -> local_make_posint i ] ]
  ;
  integer:
    [ [ i = INT      -> local_make_posint i
      | "-"; i = INT -> local_make_negint i ] ]
  ;
  numarg:
    [ [ i = INT -> Num(loc, int_of_string i) ] ]
  ;
  field:
    [ [ s = FIELD -> local_id_of_string s ] ]
  ;
  dirpath:
    [ [ id = ident; l = LIST0 field -> local_make_dirpath (local_append l id) ] ]
  ;
  fields:
    [ [ id = field; (l,id') = fields -> (local_append l id,id')
      | id = field -> ([],id)
      ] ]
  ;
  basequalid:
    [ [ id = ident; (l,id')=fields -> local_make_qualid (local_append l id) id'
      | id = ident -> local_make_short_qualid id
      ] ]
  ;
  qualid:
    [ [ qid = basequalid -> loc, qid ] ]
  ;
  reference:
    [ [ id = ident; (l,id') = fields ->
        Tacexpr.RQualid (loc, local_make_qualid (local_append l id) id')
      | id = ident -> Tacexpr.RIdent (loc,id)
      ] ]
  ;
  string:
    [ [ s = STRING -> s ] ]
  ;
  astpath:
    [ [ id = ident; (l,a) = fields ->
          Path(loc, local_make_path (local_append l id) a)
      | id = ident -> Nvar(loc, id)
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
    [ [ l = LIST0 Prim.ast -> l ] ]
  ;
END
