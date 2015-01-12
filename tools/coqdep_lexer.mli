(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type mL_token = Use_module of string

type qualid = string list

type coq_token =
    Require of qualid list
  | RequireString of string
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
