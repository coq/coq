(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

(* The => tactical *)
val tclIPAT : ssripats -> unit Proofview.tactic

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
