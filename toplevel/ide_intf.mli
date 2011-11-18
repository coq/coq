(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Interface of CoqIde calls to Coq *)

type xml = Xml_parser.xml

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

type 'a call

type raw = bool
type verbose = bool

(** Running a command (given as a string).
    - The 1st flag indicates whether to use "raw" mode
      (less sanity checks, no impact on the undo stack).
      Suitable e.g. for queries, or for the Set/Unset
      of display options that coqide performs all the time.
    - The 2nd flag controls the verbosity.
    - The returned string contains the messages produced
      by this command, but not the updated goals (they are
      to be fetch by a separated [current_goals]). *)
val interp : raw * verbose * string -> string call

(** Backtracking by at least a certain number of phrases.
    No finished proofs will be re-opened. Instead,
    we continue backtracking until before these proofs,
    and answer the amount of extra backtracking performed.
    Backtracking by more than the number of phrases already
    interpreted successfully (and not yet undone) will fail. *)
val rewind : int -> int call

(** Fetching the list of current goals *)
val goals : goals call

(** Retrieving the tactics applicable to the current goal. [None] if there is 
    no proof in progress. *)
val hints : (hint list * hint) option call

(** The status, for instance "Ready in SomeSection, proving Foo" *)
val status : status call

(** Is a directory part of Coq's loadpath ? *)
val inloadpath : string -> bool call

(** Create a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables. *)
val mkcases : string -> string list list call


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
  inloadpath : string -> bool;
  mkcases : string -> string list list;
  handle_exn : exn -> location * string;
}

val abstract_eval_call : handler -> 'a call -> 'a value

(** * XML data marshalling *)

exception Marshal_error

val of_bool : bool -> xml
val to_bool : xml -> bool

val of_string : string -> xml
val to_string : xml -> string

val of_int : int -> xml
val to_int : xml -> int

val of_pair : ('a -> xml) -> ('b -> xml) -> ('a * 'b) -> xml
val to_pair : (xml -> 'a) -> (xml -> 'b) -> xml -> ('a * 'b)

val of_list : ('a -> xml) -> 'a list -> xml
val to_list : (xml -> 'a) -> xml -> 'a list

val of_value : ('a -> xml) -> 'a value -> xml
val to_value : (xml -> 'a) -> xml -> 'a value

val of_call : 'a call -> xml
val to_call : xml -> 'a call

val of_goals : goals -> xml
val to_goals : xml -> goals

val of_answer : 'a call -> 'a value -> xml
val to_answer : xml -> 'a value

(** * Debug printing *)

val pr_call : 'a call -> string
val pr_value : 'a value -> string
val pr_full_value : 'a call -> 'a value -> string
