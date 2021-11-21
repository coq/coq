(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ssrmatching_plugin

type elim_what =
| EConstr of
        Ssrast.ssrhyp list * Ssrmatching.occ *
          EConstr.constr
| EGen of
    ((Ssrast.ssrhyp list option *
      Ssrmatching.occ) *
      Ssrmatching.cpattern)

val ssrelim :
  ?is_case:bool ->
  ((Ssrast.ssrhyps option * Ssrast.ssrocc) *
     Ssrmatching.cpattern)
    list ->
  elim_what ->
  ?elim:EConstr.constr ->
  Ssrast.ssripat option ->
  (?seed:Names.Name.t list array -> elim_what ->
   Ssrast.ssripat option ->
   unit Proofview.tactic ->
   bool -> Ssrast.ssrhyp list -> unit Proofview.tactic) ->
  unit Proofview.tactic

val elimtac : EConstr.constr -> unit Proofview.tactic

val casetac :
  EConstr.constr ->
  (?seed:Names.Name.t list array -> unit Proofview.tactic -> unit Proofview.tactic) ->
  unit Proofview.tactic

val is_injection_case : Environ.env -> Evd.evar_map -> EConstr.t -> bool
val perform_injection :
  EConstr.constr ->
  unit Proofview.tactic

val ssrscase_or_inj_tac :
  EConstr.constr ->
  unit Proofview.tactic
