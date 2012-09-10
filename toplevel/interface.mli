(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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
  goal_id : string;
  (** Unique goal identifier *)
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
  bg_goals : (goal list * goal list) list;
  (** Zipper representing the unfocussed background goals *)
}

type hint = (string * string) list
(** A list of tactics applicable and their appearance *)

type option_name = Goptionstyp.option_name

type option_value = Goptionstyp.option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string

(** Summary of an option status *)
type option_state = Goptionstyp.option_state = {
  opt_sync  : bool;
  (** Whether an option is synchronous *)
  opt_depr  : bool;
  (** Wheter an option is deprecated *)
  opt_name  : string;
  (** A short string that is displayed when using [Test] *)
  opt_value : option_value;
  (** The current value of the option *)
}

type search_constraint =
(** Whether the name satisfies a regexp (uses Ocaml Str syntax) *)
| Name_Pattern of string
(** Whether the object type satisfies a pattern *)
| Type_Pattern of string
(** Whether some subtype of object type satisfies a pattern *)
| SubType_Pattern of string
(** Whether the object pertains to a module *)
| In_Module of string list
(** Bypass the Search blacklist *)
| Include_Blacklist

(** A list of search constraints; the boolean flag is set to [false] whenever
    the flag should be negated. *)
type search_flags = (search_constraint * bool) list

(** A named object in Coq. [coq_object_qualid] is the shortest path defined for 
    the user. [coq_object_prefix] is the missing part to recover the fully 
    qualified name, i.e [fully_qualified = coq_object_prefix + coq_object_qualid].
    [coq_object_object] is the actual content of the object. *)
type 'a coq_object = {
  coq_object_prefix : string list;
  coq_object_qualid : string list;
  coq_object_object : 'a;
}

type coq_info = {
  coqtop_version : string;
  protocol_version : string;
  release_date : string;
  compile_date : string;
}

(** * Coq answers to CoqIde *)

type location = (int * int) option (* start and end of the error *)

type 'a value =
  | Good of 'a
  | Fail of (location * string)
