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

open Prim

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

if not !Options.v7 then
GEXTEND Gram
  GLOBAL: bigint qualid reference ne_string;
  field:
    [ [ s = FIELD -> local_id_of_string s ] ]
  ;
  fields:
    [ [ id = field; (l,id') = fields -> (local_append l id,id')
      | id = field -> ([],id)
      ] ]
  ;
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
  bigint: (* Negative numbers are dealt with specially *)
    [ [ i = INT -> Bignat.POS (Bignat.of_string i) ] ]
  ;
END
