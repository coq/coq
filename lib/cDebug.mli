(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type flag

type t = (unit -> Pp.t) -> unit

(** Creates a debug component, which may be used to print debug
    messages.

    A debug component is named by the string [name]. It is either
    active or inactive.

    The special component ["all"] may be used to control all components.

    There is also a special component ["backtrace"] to control
    backtrace recording.
*)
val create : name:string -> unit -> t

(** Useful when interacting with a component from code, typically when
    doing something more complicated than printing.

    Note that the printer function prints some metadata compared to
    [ fun pp -> if get_flag flag then Feedback.msg_debug (pp ()) ]
 *)
val create_full : name:string -> unit -> flag * t

val get_flag : flag -> bool

val set_flag : flag -> bool -> unit

(** [get_flags] and [set_flags] use the user syntax: a comma separated
    list of activated "component" and "-component"s. [get_flags] starts
    with "all" or "-all" and lists all components after it (even if redundant). *)
val get_flags : unit -> string

(** Components not mentioned are not affected (use the "all" component
    at the start if you want to reset everything). *)
val set_flags : string -> unit

val set_debug_all : bool -> unit

val misc : flag
val pp_misc : t
