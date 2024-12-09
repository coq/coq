(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

(** Abstract type representing a transparency state. *)
Ltac2 Type t.

(** [empty] is the empty transparency state (all constants are opaque). *)
Ltac2 @ external empty : t :=
  "rocq-runtime.plugins.ltac2" "empty_transparent_state".

(** [full] is the full transparency state (all constants are transparent). *)
Ltac2 @ external full : t :=
  "rocq-runtime.plugins.ltac2" "full_transparent_state".

(** [current ()] gives the transparency state of the goal, which is influenced
    by, e.g., the [Strategy] command, or the [with_strategy] Ltac tactic. *)
Ltac2 @ external current : unit -> t :=
  "rocq-runtime.plugins.ltac2" "current_transparent_state".
