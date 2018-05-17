(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Declarative part of the interface of CoqIde calls to Coq *)

(** * Generic structures *)

type raw = bool
type verbose = bool

(** The type of coqtop goals *)
type goal = {
  goal_id : string;
  (** Unique goal identifier *)
  goal_hyp : Pp.t list;
  (** List of hypotheses *)
  goal_ccl : Pp.t;
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
  status_proofnum : int;
  (** An id describing the state of the current proof. *)
}

type 'a pre_goals = {
  fg_goals : 'a list;
  (** List of the focussed goals *)
  bg_goals : ('a list * 'a list) list;
  (** Zipper representing the unfocused background goals *)
  shelved_goals : 'a list;
  (** List of the goals on the shelf. *)
  given_up_goals : 'a list;
  (** List of the goals that have been given up *)
}

type goals = goal pre_goals

type hint = (string * string) list
(** A list of tactics applicable and their appearance *)

type option_name = string list

type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string
  | StringOptValue of string option

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

(** Calls result *)

type location = (int * int) option (* start and end of the error *)
type state_id = Stateid.t
type route_id = Feedback.route_id

(* Obsolete *)
type edit_id  = int

(* The fail case carries the current state_id of the prover, the GUI
   should probably retract to that point *)
type 'a value =
  | Good of 'a
  | Fail of (state_id * location * Pp.t)

type ('a, 'b) union = ('a, 'b) Util.union

(* Request/Reply message protocol between Coq and CoqIde *)

(**  [add ((s,eid),(sid,v))] adds the phrase [s] with edit id [eid]
     on top of the current edit position (that is asserted to be [sid])
     verbosely if [v] is true.  The response [(id,(rc,s)] is the new state
     [id] assigned to the phrase. [rc] is [Inl] if the new
     state id is the tip of the edit point, or [Inr tip] if the new phrase
     closes a focus and [tip] is the new edit tip

     [s] used to contain Coq's console output and has been deprecated
     in favor of sending feedback, it will be removed in a future
     version of the protocol.  *)
type add_sty = (string * edit_id) * (state_id * verbose)
type add_rty = state_id * ((unit, state_id) union * string)

(** [edit_at id] declares the user wants to edit just after [id].
    The response is [Inl] if the document has been rewound to that point,
    [Inr (start,(stop,tip))] if [id] is in a zone that can be focused.
    In that case the zone is delimited by [start] and [stop] while [tip]
    is the new document [tip].  Edits made by subsequent [add] are always
    performed on top of [id]. *)
type edit_at_sty = state_id
type edit_at_rty = (unit, state_id * (state_id * state_id)) union

(** [query s id] executes [s] at state [id].

    query used to reply with the contents of Coq's console output, and
    has been deprecated in favor of sending the query answers as
    feedback. It will be removed in a future version of the protocol.
*)
type query_sty = route_id * (string * state_id)
type query_rty = unit

(** Fetching the list of current goals. Return [None] if no proof is in
    progress, [Some gl] otherwise. *)
type goals_sty = unit
type goals_rty = goals option

(** Retrieve the list of uninstantiated evars in the current proof. [None] if no
    proof is in progress. *)
type evars_sty = unit
type evars_rty = evar list option

(** Retrieving the tactics applicable to the current goal. [None] if there is
    no proof in progress. *)
type hints_sty = unit
type hints_rty = (hint list * hint) option

(** The status, for instance "Ready in SomeSection, proving Foo", the
    input boolean (if true) forces the evaluation of all unevaluated
    statements *)
type status_sty = bool
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

(** Create a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables. *)
type mkcases_sty = string
type mkcases_rty = string list list

(** Quit gracefully the interpreter. *)
type quit_sty = unit
type quit_rty = unit

(* Initialize, and return the initial state id.  The argument is the filename.
 * If its directory is not in dirpath, it adds it.  It also loads
 * compilation hints for the filename. *)
type init_sty = string option
type init_rty = state_id

type about_sty = unit
type about_rty = coq_info

type handle_exn_sty = Exninfo.iexn
type handle_exn_rty = state_id * location * Pp.t

(* Retrocompatibility stuff *)
type interp_sty = (raw * verbose) * string
(* spiwack: [Inl] for safe and [Inr] for unsafe. *)
type interp_rty = state_id * (string,string) Util.union

type stop_worker_sty = string
type stop_worker_rty = unit

type print_ast_sty = state_id
type print_ast_rty = Xml_datatype.xml

type annotate_sty = string
type annotate_rty = Xml_datatype.xml

type wait_sty = unit
type wait_rty = unit

type handler = {
  add         : add_sty         -> add_rty;
  edit_at     : edit_at_sty     -> edit_at_rty;
  query       : query_sty       -> query_rty;
  goals       : goals_sty       -> goals_rty;
  evars       : evars_sty       -> evars_rty;
  hints       : hints_sty       -> hints_rty;
  status      : status_sty      -> status_rty;
  search      : search_sty      -> search_rty;
  get_options : get_options_sty -> get_options_rty;
  set_options : set_options_sty -> set_options_rty;
  mkcases     : mkcases_sty     -> mkcases_rty;
  about       : about_sty       -> about_rty;
  stop_worker : stop_worker_sty -> stop_worker_rty;
  print_ast   : print_ast_sty   -> print_ast_rty;
  annotate    : annotate_sty    -> annotate_rty;
  handle_exn  : handle_exn_sty  -> handle_exn_rty;
  init        : init_sty        -> init_rty;
  quit        : quit_sty        -> quit_rty;
  (* for internal use (fake_id) only, do not use *)
  wait        : wait_sty        -> wait_rty;
  (* Retrocompatibility stuff *)
  interp      : interp_sty      -> interp_rty;
}

