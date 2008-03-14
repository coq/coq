(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo" i*)

(*i $Id$ i*)

open Pcoq
open Names
open Libnames
open Topconstr

let prim_kw = ["{"; "}"; "["; "]"; "("; ")"; "'"]
let _ = List.iter (fun s -> Lexer.add_token("",s)) prim_kw

open Prim
open Nametab

let local_make_qualid l id = make_qualid (make_dirpath l) id

GEXTEND Gram
  GLOBAL: 
    bigint natural integer identref name ident var preident
    fullyqualid qualid reference dirpath
    ne_string string pattern_ident pattern_identref;
  preident:
    [ [ s = IDENT -> s ] ]
  ;
  ident:
    [ [ s = IDENT -> id_of_string s ] ]
  ;
  pattern_ident:
    [ [ s = PATTERNIDENT -> id_of_string s ] ]
  ;
  pattern_identref:
    [ [ id = pattern_ident -> (loc, id) ] ]
  ;
  var: (* as identref, but interpret as a term identifier in ltac *)
    [ [ id = ident -> (loc,id) ] ]
  ;
  identref:
    [ [ id = ident -> (loc,id) ] ]
  ;
  field:
    [ [ s = FIELD -> id_of_string s ] ]
  ;
  fields:
    [ [ id = field; (l,id') = fields -> (l@[id],id')
      | id = field -> ([],id)
      ] ]
  ;
  fullyqualid:
    [ [ id = ident; (l,id')=fields -> loc,id::List.rev (id'::l)
      | id = ident -> loc,[id]
      ] ]
  ;
  basequalid:
    [ [ id = ident; (l,id')=fields -> local_make_qualid (l@[id]) id'
      | id = ident -> make_short_qualid id
      ] ]
  ;
  name:
    [ [ IDENT "_" -> (loc, Anonymous)
      | id = ident -> (loc, Name id) ] ]
  ;
  reference:
    [ [ id = ident; (l,id') = fields ->
        Qualid (loc, local_make_qualid (l@[id]) id')
      | id = ident -> Ident (loc,id)
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
  dirpath:
    [ [ id = ident; l = LIST0 field ->
        make_dirpath (l@[id]) ] ]
  ;
  string:
    [ [ s = STRING -> s ] ]
  ;
  integer:
    [ [ i = INT      -> int_of_string i
      | "-"; i = INT -> - int_of_string i ] ]
  ;
  natural:
    [ [ i = INT -> int_of_string i ] ]
  ;
  bigint: (* Negative numbers are dealt with specially *)
    [ [ i = INT -> (Bigint.of_string i) ] ]
  ;
END
