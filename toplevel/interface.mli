(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Declarative part of the interface of CoqIde calls to Coq *)

(** * Generic structures *)

type raw = bool
type verbose = bool

type goal = {
  goal_hyp : string list;
  goal_ccl : string;
}

type status = {
  status_path : string option;
  status_proofname : string option;
}

type goals =
  | No_current_proof
  | Proof_completed
  | Unfocused_goals of goal list
  | Uninstantiated_evars of string list
  | Goals of goal list

type hint = (string * string) list

type option_name = Goptions.option_name

type option_value = Goptions.option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string

type option_state = Goptions.option_state = {
  opt_sync  : bool;
  opt_depr  : bool;
  opt_name  : string;
  opt_value : option_value;
}

(** * Coq answers to CoqIde *)

type location = (int * int) option (* start and end of the error *)

type 'a value =
  | Good of 'a
  | Fail of (location * string)

(** * The structure that coqtop should implement *)

type handler = {
  interp : raw * verbose * string -> string;
  rewind : int -> int;
  goals : unit -> goals;
  hints : unit -> (hint list * hint) option;
  status : unit -> status;
  get_options : unit -> (option_name * option_state) list;
  set_options : (option_name * option_value) list -> unit;
  inloadpath : string -> bool;
  mkcases : string -> string list list;
  handle_exn : exn -> location * string;
}
