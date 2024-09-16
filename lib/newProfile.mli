(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module MiniJson : sig
  (** Subtype of Yojson.Safe.t *)
  type t = [
    | `Intlit of string
    | `String of string
    | `Assoc of (string * t) list
    | `List of t list
  ]
end

val profile : string -> ?args:(unit -> (string * MiniJson.t) list) -> (unit -> 'a) -> unit -> 'a
(** Profile the given function.

    [args] is called only if profiling is active, it is used to
    produce additional annotations.
*)

type profile_pair = ProfPair : { enter : unit -> 'a; leave : 'a -> unit } -> profile_pair

val profile_pair : string -> ?args:(unit -> (string * MiniJson.t) list) -> unit -> profile_pair option
(** Low level API: [enter] should be called at the start of a
    profiling component and [leave] at the exit (including exiting by
    raised exception).

    You can reuse them as long as [is_profiling] doesn't change.
*)

val is_profiling : unit -> bool

type settings =
  { output : Format.formatter;
    fname : string;
  }

val init : settings -> unit
(** Profiling must not be active.
    Activates profiling with a fresh state. *)

val finish : unit -> unit
(** Profiling must be active.
    Deactivates profiling. *)

type accu
(** Profiling state accumulator. *)

val pause : unit -> accu option
(** Returns [None] if profiling is inactive.
    Deactivates profiling if it is active, returning the current state. *)

val resume : accu -> unit
(** Profiling must not be active.
    Activates profiling with the given state. *)

type sums
(** Timings for sub-events *)

val with_profiling : (unit -> 'a) -> MiniJson.t list * sums * 'a
(** Runs the given function with profiling active and returns the
    produced events and sum times of subevents. *)

val insert_results : MiniJson.t list -> sums -> unit
(** Profiling must be active.
    Outputs the given events and includes the sum times in the current event. *)
