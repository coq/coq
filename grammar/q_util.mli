(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open GramCompat (* necessary for camlp4 *)

type argument_type =
| ListArgType of argument_type
| OptArgType of argument_type
| PairArgType of argument_type * argument_type
| ExtraArgType of string

type user_symbol =
| Ulist1 of user_symbol
| Ulist1sep of user_symbol * string
| Ulist0 of user_symbol
| Ulist0sep of user_symbol * string
| Uopt of user_symbol
| Uentry of string
| Uentryl of string * int

type extend_token =
| ExtTerminal of string
| ExtNonTerminal of user_symbol * string

val mlexpr_of_list :  ('a -> MLast.expr) -> 'a list -> MLast.expr

val mlexpr_of_pair :
  ('a -> MLast.expr) -> ('b -> MLast.expr)
    -> 'a * 'b -> MLast.expr

val mlexpr_of_bool : bool -> MLast.expr

val mlexpr_of_int : int -> MLast.expr

val mlexpr_of_string : string -> MLast.expr

val mlexpr_of_option : ('a -> MLast.expr) -> 'a option -> MLast.expr

val mlexpr_of_prod_entry_key : (string -> MLast.expr) -> user_symbol -> MLast.expr

val type_of_user_symbol : user_symbol -> argument_type

val parse_user_entry : string -> string -> user_symbol

val string_of_user_entry : user_symbol -> string * string
