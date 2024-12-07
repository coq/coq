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
Require Ltac2.TransparentState.

(** [unify ts c1 c2] unifies [c1] and [c2] (using Evarconv unification), which
    may have the effect of instantiating evars. If the [c1] and [c2] cannot be
    unified, an [Internal] exception is raised. *)
Ltac2 @ external unify : TransparentState.t -> constr -> constr -> unit :=
  "rocq-runtime.plugins.ltac2" "evarconv_unify".

(** [unify_with_full_ts] is like [unify TransparentState.full]. *)
Ltac2 unify_with_full_ts : constr -> constr -> unit := fun c1 c2 =>
  unify TransparentState.full c1 c2.

(** [unify_with_current_ts] is like [unify (TransparentState.current ())]. *)
Ltac2 unify_with_current_ts : constr -> constr -> unit := fun c1 c2 =>
  unify (TransparentState.current ()) c1 c2.
