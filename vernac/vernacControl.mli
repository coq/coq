(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Partially interpreted control flags. *)
type 'state control_entry

type 'state control_entries = 'state control_entry list

(** Translate from syntax and add default timeout. *)
val from_syntax : Vernacexpr.control_flag list -> unit control_entries

type ('st0,'st) with_local_state = { with_local_state : 'a. 'st0 -> (unit -> 'a) -> 'st * 'a }
(** [with_local_state state0 f] should run [f] with [state0] installed,
    capture the state produced by running [f] and revert the global state afterwards.
*)

val trivial_state : (unit,unit) with_local_state

(** [under_control ~loc ~with_local_state control ~noop f]
    runs [f ()] in the context given by the [control].

    If the [control] cause execution to end with no more work to be
    done and no error (eg [Fail] when [f] raised an exception) then
    [noop] is returned.
*)
val under_control : loc:Loc.t option ->
  with_local_state:('state0,'state) with_local_state ->
  'state0 control_entries ->
  noop:'b ->
  (unit -> 'b) ->
  'state control_entries * 'b

(** Print any final messages (eg from [Time]) and raise final
    exceptions (eg from [Fail] when the command did not fail). The
    returned boolean tells if we should be noop ([Fail] where the
    command failed or [Succeed] where it succeeded).
*)
val after_last_phase : loc:Loc.t option -> _ control_entries -> bool
