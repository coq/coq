(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Interface to coqmod's lexer *)
type qualid = string list

type load = Logical of string | Physical of string

type coq_token =
  | Require of qualid option * qualid list
  | Declare of string list
  | Load of load
  | External of qualid * string

exception Fin_fichier
exception Syntax_error of int*int

type t

val lex_coq : file:string -> Lexing.lexbuf -> t
val next_token : t -> coq_token
