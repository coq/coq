(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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

type t
(** Type of backtraces. They're essentially stack of frames. *)

val empty : t
(** Empty frame stack. *)

val push : t -> t
(** Add the current backtrace information to a given backtrace. *)

val repr : t -> frame list
(** Represent a backtrace as a list of frames. Leftmost element is the outermost
    call. *)

(** {5 Utilities} *)

val print_frame : frame -> string
(** Represent a frame. *)

(** {5 Exception handling} *)

val record_backtrace : bool -> unit
(** Whether to activate the backtrace recording mechanism. Note that it will
    only work whenever the program was compiled with the [debug] flag. *)

val get_backtrace : Exninfo.info -> t option
(** Retrieve the optional backtrace coming with the exception. *)

val add_backtrace : exn -> Exninfo.iexn
(** Add the current backtrace information to the given exception.

    The intended use case is of the form: {[

    try foo
      with
      | Bar -> bar
      | err -> let err = add_backtrace err in baz

    ]}

    WARNING: any intermediate code between the [with] and the handler may
    modify the backtrace. Yes, that includes [when] clauses. Ideally, what you
    should do is something like: {[

    try foo
      with err ->
        let err = add_backtrace err in
        match err with
        | Bar -> bar
        | err -> baz

    ]}

    I admit that's a bit heavy, but there is not much to do...

*)

val app_backtrace : src:Exninfo.info -> dst:Exninfo.info -> Exninfo.info
(** Append the backtrace from [src] to [dst]. The returned exception is [dst]
    except for its backtrace information. This is targeted at container
    exceptions, that is, exceptions that contain exceptions. This way, one can
    transfer the backtrace from the container to the underlying exception, as if
    the latter was the one originally raised. *)
