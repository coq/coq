(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val goal_selector : Goal_select.t Pcoq.Entry.t

val toplevel_selector : Goal_select.t Pcoq.Entry.t

val wit_ltac_selector : (Goal_select.t, unit, unit) Genarg.genarg_type

val ltac_selector : Goal_select.t Pcoq.Entry.t

val wit_ltac_use_default : (bool, unit, unit) Genarg.genarg_type

val ltac_use_default : bool Pcoq.Entry.t
