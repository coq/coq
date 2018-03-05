(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type mL_token = Use_module of string

type qualid = string list

type coq_token =
    Require of qualid option * qualid list
  | Declare of string list
  | Load of string
  | AddLoadPath of string
  | AddRecLoadPath of string * qualid

exception Fin_fichier
exception Syntax_error of int * int

val coq_action : Lexing.lexbuf -> coq_token
val caml_action : Lexing.lexbuf -> mL_token
val mllib_list : Lexing.lexbuf -> string list
val ocamldep_parse : Lexing.lexbuf -> string list
