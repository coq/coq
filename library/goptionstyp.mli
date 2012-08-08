(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Some types used in the generic option mechanism (Goption) *)

(** Placing them here in a pure interface avoid some dependency issues
    when compiling CoqIDE *)

type option_name = string list

type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string

type option_state = {
  opt_sync  : bool;
  opt_depr  : bool;
  opt_name  : string;
  opt_value : option_value;
}
