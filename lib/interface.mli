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

(** The type of coqtop goals *)
type goal = {
  goal_hyp : string list;
  (** List of hypotheses *)
  goal_ccl : string;
  (** Goal conclusion *)
}

type evar = {
  evar_info : string;
  (** A string describing an evar: type, number, environment *)
}

type status = {
  status_path : string list;
  (** Module path of the current proof *)
  status_proofname : string option;
  (** Current proof name. [None] if no focussed proof is in progress *)
  status_allproofs : string list;
  (** List of all pending proofs. Order is not significant *)
  status_statenum : int;
  (** A unique id describing the state of coqtop *)
  status_proofnum : int;
  (** An id describing the state of the current proof. *)
}

type goals = {
  fg_goals : goal list;
  (** List of the focussed goals *)
  bg_goals : goal list;
  (** List of the background goals *)
}

type hint = (string * string) list
(** A list of tactics applicable and their appearance *)

type option_name = string list

type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string

(** Summary of an option status *)
type option_state = {
  opt_sync  : bool;
  (** Whether an option is synchronous *)
  opt_depr  : bool;
  (** Wheter an option is deprecated *)
  opt_name  : string;
  (** A short string that is displayed when using [Test] *)
  opt_value : option_value;
  (** The current value of the option *)
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
  goals : unit -> goals option;
  evars : unit -> evar list option;
  hints : unit -> (hint list * hint) option;
  status : unit -> status;
  get_options : unit -> (option_name * option_state) list;
  set_options : (option_name * option_value) list -> unit;
  inloadpath : string -> bool;
  mkcases : string -> string list list;
  handle_exn : exn -> location * string;
}
