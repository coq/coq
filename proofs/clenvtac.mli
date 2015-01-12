(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
val unify : ?flags:unify_flags -> constr -> unit Proofview.tactic
val clenv_refine : evars_flag -> ?with_classes:bool -> clausenv -> unit Proofview.tactic
val res_pf : ?with_evars:evars_flag -> ?with_classes:bool -> ?flags:unify_flags -> clausenv -> unit Proofview.tactic

val clenv_pose_dependent_evars : evars_flag -> clausenv -> clausenv
val clenv_value_cast_meta : clausenv -> constr
