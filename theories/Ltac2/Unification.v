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


(** This file contains conversion and unification.
    Both can add universe constraints.
    Compared to conversion, unification can additionaly instantiate evars.
*)


  (** Conversion  **)

(** Controls if cumulativity Prop <= Set <= Type 1 <= ... <= Type i <= ... is used for conversion. *)
Ltac2 Type conv_flag := [
| CONV
| CUMUL
].

(** Conv returns true if both terms are convertible, in which case it updates the
    environment with the universes constraints required for the terms to be convertible.
    It returns false if the terms are not convertible.
    It fails if there is more than one goal under focus.

    Conv is parametrised by:
    - conv_flag which controls if conversion is done up to cumulativity or not
    - TransparentState.t which controls which constants get unfolded during conversion
*)
Ltac2 @external conv : conv_flag -> TransparentState.t -> constr -> constr -> bool
  := "rocq-runtime.plugins.ltac2" "infer_conv".

(** It only unfolds constants that are transparent in the current state *)
Ltac2 conv_current : constr -> constr -> bool := fun c1 c2 => conv CONV (TransparentState.current ()) c1 c2.

(** All constants are considered as transparents when doing conversion *)
Ltac2 conv_full : constr -> constr -> bool := fun c1 c2 => conv CONV TransparentState.full c1 c2.


  (** Unification **)

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

(** [solve_constraints ()] solves any delayed unification constraints. *)
Ltac2 @external solve_constraints : unit -> unit
  := "rocq-runtime.plugins.ltac2" "solve_constraints".

Module UnsafeEnv.

  (** [conv_in_env] returns true if both terms are convertible in the given environment,
      in which case it updates the proof state with the universes constraints
      required for the terms to be convertible.
      It returns false if the terms are not convertible.
      It fails if there is more than one goal under focus.

      [conv_in_env] is parametrised by:
      - Unification.conv_flag which controls if conversion is done up to cumulativity or not
      - TransparentState.t which controls which constants get unfolded during conversion
   *)
  Ltac2 @external conv_in_env : Unification.conv_flag -> TransparentState.t -> env -> constr -> constr -> bool
    := "rocq-runtime.plugins.ltac2" "infer_conv_in_env".

  (** [unify_in_env pb ts ctx c1 c2] unifies [c1] and [c2] in [ctx] (using Evarconv unification),
      which may have the effect of instantiating evars.
      If the [c1] and [c2] cannot be unified, an [Internal] exception is raised. *)
  Ltac2 @external unify_in_env : Unification.conv_flag -> TransparentState.t -> env -> constr -> constr -> unit
    := "rocq-runtime.plugins.ltac2" "evarconv_unify_in_env".

End UnsafeEnv.
