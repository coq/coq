(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
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

(** Coq unstructured messages *)

type message_level =
  | Debug of string
  | Info
  | Notice
  | Warning
  | Error

type message = {
  message_level : message_level;
  message_content : string;
}

(** Coq "semantic" infos obtained during parsing/execution *)
type edit_id = int

type feedback_content =
  | AddedAxiom
  | Processed
  | GlobRef of (int*int) * string * string * string * string

type feedback = {
  edit_id : edit_id;
  content : feedback_content;
}

(** Calls result *)

type location = (int * int) option (* start and end of the error *)

type 'a value =
  | Good of 'a
  | Fail of (location * string)

(* Request/Reply message protocol between Coq and CoqIde *)

(** Running a command (given as its id and its text).
    "raw" mode (less sanity checks, no impact on the undo stack)
    is suitable for queries, or for the Set/Unset
    of display options that coqide performs all the time.
    The returned string contains the messages produced
    but not the updated goals (they are
    to be fetch by a separated [current_goals]). *)
type interp_sty = edit_id * raw * verbose * string
type interp_rty = string

(** Backtracking by at least a certain number of phrases.
    No finished proofs will be re-opened. Instead,
    we continue backtracking until before these proofs,
    and answer the amount of extra backtracking performed.
    Backtracking by more than the number of phrases already
    interpreted successfully (and not yet undone) will fail. *)
type rewind_sty = int
type rewind_rty = int

(** Fetching the list of current goals. Return [None] if no proof is in
    progress, [Some gl] otherwise. *)
type goals_sty = unit
type goals_rty = goals option

(** Retrieve the list of unintantiated evars in the current proof. [None] if no
    proof is in progress. *)
type evars_sty = unit
type evars_rty = evar list option

(** Retrieving the tactics applicable to the current goal. [None] if there is
    no proof in progress. *)
type hints_sty = unit
type hints_rty = (hint list * hint) option

(** The status, for instance "Ready in SomeSection, proving Foo" *)
type status_sty = unit
type status_rty = status

(** Search for objects satisfying the given search flags. *)
type search_sty = search_flags
type search_rty = string coq_object list

(** Retrieve the list of options of the current toplevel *)
type get_options_sty = unit
type get_options_rty = (option_name * option_state) list

(** Set the options to the given value. Warning: this is not atomic, so whenever
    the call fails, the option state can be messed up... This is the caller duty
    to check that everything is correct. *)
type set_options_sty = (option_name * option_value) list
type set_options_rty = unit

(** Is a directory part of Coq's loadpath ? *)
type inloadpath_sty = string
type inloadpath_rty = bool

(** Create a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables. *)
type mkcases_sty = string
type mkcases_rty = string list list

(** Quit gracefully the interpreter. *)
type quit_sty = unit
type quit_rty = unit

type about_sty = unit
type about_rty = coq_info

type handle_exn_rty = location * string
type handle_exn_sty = exn

type handler = {
  interp      : interp_sty      -> interp_rty;
  rewind      : rewind_sty      -> rewind_rty;
  goals       : goals_sty       -> goals_rty;
  evars       : evars_sty       -> evars_rty;
  hints       : hints_sty       -> hints_rty;
  status      : status_sty      -> status_rty;
  search      : search_sty      -> search_rty;
  get_options : get_options_sty -> get_options_rty;
  set_options : set_options_sty -> set_options_rty;
  inloadpath  : inloadpath_sty  -> inloadpath_rty;
  mkcases     : mkcases_sty     -> mkcases_rty;
  quit        : quit_sty        -> quit_rty;
  about       : about_sty       -> about_rty;
  handle_exn  : handle_exn_sty  -> handle_exn_rty;
}

