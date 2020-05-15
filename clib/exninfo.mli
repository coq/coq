(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Additional information worn by exceptions. *)

type 'a t
(** Information containing a given type. *)

type info
(** All information *)

type iexn = exn * info
(** Information-wearing exceptions *)

val make : unit -> 'a t
(** Create a new piece of information. *)

val null : info
(** No information *)

val add : info -> 'a t -> 'a -> info
(** Add information to an exception. *)

val get : info -> 'a t -> 'a option
(** Get information worn by an exception. Returns [None] if undefined. *)

val info : exn -> info
(** Retrieve the information of the last exception raised. *)

type backtrace

val get_backtrace : info -> backtrace option
(** [get_backtrace info] does get the backtrace associated to info *)

val backtrace_to_string : backtrace -> string
(** [backtrace_to_string info] does get the backtrace associated to info *)

val record_backtrace : bool -> unit

val capture : exn -> iexn
(** Add the current backtrace information to the given exception.

    The intended use case is of the form: {[

    try foo
    with
    | Bar -> bar
    | exn ->
      let exn = Exninfo.capture err in
      baz

    ]}

    where [baz] should re-raise using [iraise] below.

    WARNING: any intermediate code between the [with] and the handler may
    modify the backtrace. Yes, that includes [when] clauses. Ideally, what you
    should do is something like: {[

    try foo
    with exn ->
      let exn = Exninfo.capture exn in
      match err with
      | Bar -> bar
      | err -> baz

    ]}

    I admit that's a bit heavy, but there is not much to do...

*)

val iraise : iexn -> 'a
(** Raise the given enriched exception. *)

val reify : unit -> info
