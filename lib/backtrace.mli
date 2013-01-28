(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Low-level management of OCaml backtraces.

  Currently, OCaml manages its backtraces in a very imperative way. That is to
  say, it only keeps track of the stack destroyed by the last raised exception.
  So we have to be very careful when using this module not to do silly things.

  Basically, you need to manually handle the reraising of exceptions. In order
  to do so, each time the backtrace is lost, you must [push] the stack fragment.
  This essentially occurs whenever a [with] handler is crossed.

*)

(** {5 Backtrace information} *)

type location = {
  loc_filename : string;
  loc_line : int;
  loc_start : int;
  loc_end : int;
}
(** OCaml debugging information for function calls. *)

type frame = { frame_location : location option; frame_raised : bool; }
(** A frame contains two informations: its optional physical location, and
    whether it raised the exception or let it pass through. *)

type t = frame list option
(** Type of backtraces. They're just stack of frames. [None] indicates that we
    don't care about recording the backtraces. *)

val empty : t
(** Empty frame stack. *)

val none : t
(** Frame stack that will not register anything. *)

val push : t -> t
(** Add the current backtrace information to a given backtrace. *)

(** {5 Utilities} *)

val print_frame : frame -> string
(** Represent a frame. *)

(** {5 Exception handling} *)

val register_backtrace_handler : (exn -> exn option) -> unit
(** Add a handler to enrich backtrace information that may be carried by
    exceptions. If the handler returns [None], this means that it is not its
    duty to handle this one. Otherwise, the new exception will be used by the
    functions thereafter instead of the original one.

    Handlers are called in the reverse order of their registration. If no
    handler match, the original exception is returned.
*)

val push_exn : exn -> exn
(** Add the current backtrace information to the given exception, using the
    registered handlers.

    The intended use case is of the form: {[

    try foo
      with
      | Bar -> bar
      | err -> let err = push_exn err in baz

    ]}

    WARNING: any intermediate code between the [with] and the handler may
    modify the backtrace. Yes, that includes [when] clauses. Ideally, what you
    should do is something like: {[

    try foo
      with err ->
        let err = push_exn err in
        match err with
        | Bar -> bar
        | err -> baz

    ]}

    I admit that's a bit heavy, but there is not much to do...

*)

val reraise : exn -> 'a
(** Convenience function which covers a generic pattern in Coq code.
    [reraise e] is equivalent to [raise (push_exn e)].

    The intended use case is of the form: {[

    try foo
      with
      | Bar -> bar
      | err -> reraise err

    ]}

*)
