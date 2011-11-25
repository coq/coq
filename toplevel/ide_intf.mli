(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Applicative part of the interface of CoqIde calls to Coq *)

open Interface

type xml = Xml_parser.xml

type 'a call

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

val abstract_eval_call : handler -> 'a call -> 'a value

(** * XML data marshalling *)

exception Marshal_error

val of_value : ('a -> xml) -> 'a value -> xml
val to_value : (xml -> 'a) -> xml -> 'a value

val of_call : 'a call -> xml
val to_call : xml -> 'a call

val of_answer : 'a call -> 'a value -> xml
val to_answer : xml -> 'a value

(** * Debug printing *)

val pr_call : 'a call -> string
val pr_value : 'a value -> string
val pr_full_value : 'a call -> 'a value -> string
