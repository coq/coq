(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type qualid = string list

type coq_token =
  | Require of qualid option * qualid list
  | Declare of string list
  | Load of string
  | AddLoadPath of string
  | AddRecLoadPath of string * qualid

exception Fin_fichier
exception Syntax_error of int * int

val coq_action : Lexing.lexbuf -> coq_token
