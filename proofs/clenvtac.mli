(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Clenv
open Proof_type
open Tacexpr
open Unification

(** Tactics *)
val unify : ?flags:unify_flags -> constr -> tactic
val clenv_refine : evars_flag -> ?with_classes:bool -> clausenv -> tactic
val res_pf : clausenv -> ?with_evars:evars_flag -> ?flags:unify_flags -> tactic

val clenv_pose_dependent_evars : evars_flag -> clausenv -> clausenv
val clenv_value_cast_meta : clausenv -> constr
