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
open Names
open Libnames
open Topconstr

let _ =
  if not !Options.v7 then
    Pcoq.reset_all_grammars()
let _ =
  if not !Options.v7 then
  let f = Gram.Unsafe.clear_entry in
  f Prim.bigint;
  f Prim.qualid;
  f Prim.ast;
  f Prim.reference

let prim_kw = ["{"; "}"; "["; "]"; "("; ")"; "<>"; "<<"; ">>"; "'"]
let _ = 
  if not !Options.v7 then
    List.iter (fun s -> Lexer.add_token("",s)) prim_kw

ifdef Quotify then
open Qast

open Prim

ifdef Quotify then
module Prelude = struct
let local_id_of_string s = Apply ("Names","id_of_string", [s])
let local_make_dirpath l = Qast.Apply ("Names","make_dirpath",[l])
let local_make_posint s = s
let local_make_negint s = Apply ("Pervasives","~-", [s])
let local_make_qualid l id' = 
  Qast.Apply ("Nametab","make_qualid", [local_make_dirpath l;id'])
let local_make_short_qualid id =
  Qast.Apply ("Nametab","make_short_qualid",[id])
let local_make_path l id' =
  Qast.Apply ("Libnames","encode_kn", [local_make_dirpath l;id'])
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
let local_make_path l a = encode_kn (local_make_dirpath l) a
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

if not !Options.v7 then
GEXTEND Gram
  GLOBAL: (*ast*) bigint qualid reference ne_string;
(*
  metaident:
    [ [ s = METAIDENT -> Nmeta (loc,s) ] ]
  ;
*)
  field:
    [ [ s = FIELD -> local_id_of_string s ] ]
  ;
  fields:
    [ [ id = field; (l,id') = fields -> (local_append l id,id')
      | id = field -> ([],id)
      ] ]
  ;
(*
  astpath:
    [ [ id = base_ident; (l,a) = fields ->
          Path(loc, local_make_path (local_append l id) a)
      | id = base_ident -> Nvar(loc, id)
      ] ]
  ;
*)
  basequalid:
    [ [ id = base_ident; (l,id')=fields ->
          local_make_qualid (local_append l id) id'
      | id = base_ident -> local_make_short_qualid id
      ] ]
  ;
  reference:
    [ [ id = base_ident; (l,id') = fields ->
        Qualid (loc, local_make_qualid (local_append l id) id')
      | id = base_ident -> Ident (loc,id)
      ] ]
  ;
  qualid:
    [ [ qid = basequalid -> loc, qid ] ]
  ;
  ne_string:
    [ [ s = STRING -> 
        if s="" then Util.user_err_loc(loc,"",Pp.str"Empty string"); s
    ] ]
  ;
(*
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
      | "'"; a = ast -> Node(loc,"$QUOTE",[a]) ] ]
  ;
*)
  bigint: (* Negative numbers are dealt with specially *)
    [ [ i = INT -> Bignat.POS (Bignat.of_string i) ] ]
  ;
END

(*
let constr_to_ast a =
  Termast.ast_of_rawconstr
    (Constrintern.interp_rawconstr Evd.empty (Global.env()) a)

let constr_parser_with_glob = Pcoq.map_entry constr_to_ast Constr.constr

let _ = define_ast_quotation true "constr" constr_parser_with_glob
*)
