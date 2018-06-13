(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Legacy components of the previous proof engine. *)

open Clenv
open EConstr
open Unification

(** Tactics *)
val unify : ?flags:unify_flags -> constr -> unit Proofview.tactic
val clenv_refine : ?with_evars:bool -> ?with_classes:bool -> clausenv -> unit Proofview.tactic
val res_pf : ?with_evars:bool -> ?with_classes:bool -> ?flags:unify_flags -> clausenv -> unit Proofview.tactic

val clenv_pose_dependent_evars : ?with_evars:bool -> clausenv -> clausenv
val clenv_value_cast_meta : clausenv -> constr
