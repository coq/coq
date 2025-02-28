(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init Std.

(** Env: contains section variables and hypotheses. *)

(* Could also handle local variables (Rel)?
   push_rel would probably be marked unsafe,
   because if "e" is valid in "env"
   then it is also valid in "push_named x t env",
   but not necessarily in "push_rel x t env". *)

Ltac2 @external global_env : unit -> env := "rocq-runtime.plugins.ltac2" "global_env".
(** Returns the global env, containing section variables (even if
    they were cleared) and no variables local to the proof. *)

Ltac2 @external goal_env : unit -> env := "rocq-runtime.plugins.ltac2" "goal_env".
(** Panics if there is not exactly one goal under focus. Otherwise
    returns the env of this goal. *)

Ltac2 @external current_env : unit -> env := "rocq-runtime.plugins.ltac2" "current_env".
(** If there is no goal under focus, [global_env()].
    If there is 1 goal under focus, [goal_env()].
    Panics if there is more than 1 goal under focus. *)

Ltac2 @external push_named_assum : binder -> env -> env
  := "rocq-runtime.plugins.ltac2" "push_named_assum".
(** [push_named bnd ctx] where [bnd] is [x : t] produces [ctx, x : t].
    [x] must not be anonymous and must be fresh in [ctx]. *)

Ltac2 @external hyp_in : env -> ident -> constr := "rocq-runtime.plugins.ltac2" "hyp_in".

Ltac2 @external hyp_value_in : env -> ident -> constr option
  := "rocq-runtime.plugins.ltac2" "hyp_value_in".

Ltac2 @external hyps_in : env -> (ident * constr option * constr) list
  := "rocq-runtime.plugins.ltac2" "hyps_in".

Ltac2 @ external get : ident list -> Std.reference option := "rocq-runtime.plugins.ltac2" "env_get".
(** Returns the global reference corresponding to the absolute name given as
    argument if it exists. *)

Ltac2 @ external expand : ident list -> Std.reference list := "rocq-runtime.plugins.ltac2" "env_expand".
(** Returns the list of all global references whose absolute name contains
    the argument list as a suffix. *)

Ltac2 @ external path : Std.reference -> ident list := "rocq-runtime.plugins.ltac2" "env_path".
(** Returns the absolute name of the given reference. Panics if the reference
    does not exist (except for VarRef). *)

Ltac2 @ external instantiate : Std.reference -> constr := "rocq-runtime.plugins.ltac2" "env_instantiate".
(** Returns a fresh instance of the corresponding reference, in particular
    generating fresh universe variables and constraints when this reference is
    universe-polymorphic. *)

Module Unsafe.

  Ltac2 @external push_named_def : binder -> constr -> env -> env
    := "rocq-runtime.plugins.ltac2" "push_named_def".
  (** [push_named_def bnd v ctx] where [bnd] is [x : t] produces [ctx, x := v : t].
      [x] must not be anonymous and must be fresh in [ctx].
      Unsafe: does not check that [v] has type [t]. *)

End Unsafe.
