(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file implements:
   - the [=>] tactical
   - the [:] pseudo-tactical for move, case, elim and abstract

   Putting these two features in the same file lets one hide much of the
   interaction between [tac E:] and [=>] ([E] has to be processed by [=>],
   not by [:]
*)

open Ssrast

(* Atomic operations for the IPat machine. Use this if you are "patching" an
 * ipat written by the user, since patching it at he AST level and then
 * compiling it may have tricky effects, eg adding a clear in front of a view
 * also has the effect of disposing the view (the compilation phase takes care
 * of this, by using the compiled ipats you can be more precise *)
type ssriop =
  | IOpId of Names.Id.t
  | IOpDrop
  | IOpTemporay
  | IOpInaccessible of string option
  | IOpInaccessibleAll
  | IOpAbstractVars of Names.Id.t list
  | IOpFastNondep

  | IOpInj of ssriops list

  | IOpDispatchBlock of id_block
  | IOpDispatchBranches of ssriops list

  | IOpCaseBlock of id_block
  | IOpCaseBranches of ssriops list

  | IOpRewrite of ssrocc * ssrdir
  | IOpView of ssrclear option * ssrview (* extra clears to be performed *)

  | IOpClear of ssrclear * ssrhyp option
  | IOpSimpl of ssrsimpl

  | IOpEqGen of unit Proofview.tactic (* generation of eqn *)

  | IOpNoop

and ssriops = ssriop list

val tclCompileIPats : ssripats -> ssriops

(* The => tactical *)
val tclIPAT : ssriops -> unit Proofview.tactic

(* As above but with the SSR exception: first case is dispatch *)
val tclIPATssr : ssripats -> unit Proofview.tactic

(* Wrappers to deal with : and eqn generation/naming:
     [tac E: gens => ipats]
   where [E] is injected into [ipats] (at the right place) and [gens] are
   generalized before calling [tac] *)
val ssrmovetac : ssrdgens ssrmovearg -> unit Proofview.tactic
val ssrsmovetac : unit Proofview.tactic
val ssrelimtac : ssrdgens ssrmovearg -> unit Proofview.tactic
val ssrselimtoptac : unit Proofview.tactic
val ssrcasetac : ssrdgens ssrmovearg -> unit Proofview.tactic
val ssrscasetoptac : unit Proofview.tactic

(* The implementation of abstract: is half here, for the [[: var ]]
 * ipat, and in ssrfwd for the integration with [have] *)
val ssrabstract : ssrdgens -> unit Proofview.tactic

(* Handling of [[:var]], needed in ssrfwd. Since ssrfwd is still outside the
 * tactic monad we export code with the V82 interface *)
module Internal : sig
val examine_abstract :
  EConstr.t -> Goal.goal Evd.sigma -> EConstr.types * EConstr.t array
val pf_find_abstract_proof :
  bool -> Goal.goal Evd.sigma -> Constr.constr -> Evar.t
end
