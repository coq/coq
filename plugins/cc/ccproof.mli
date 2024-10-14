(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ccalgo
open Constr

type rule =
| Ax of axiom
  (** if ⊢ t = u :: A, then ⊢ t = u :: A *)
| SymAx of axiom
  (** if ⊢ t = u : A, then ⊢ u = t :: A *)
| Refl of ATerm.t (* ⊢ t = t :: A *)
| Trans of proof * proof
  (** ⊢ t = u :: A -> ⊢ u = v :: A -> ⊢ t = v :: A *)
| Congr of proof * proof
  (** ⊢ f = g :: forall x : A, B -> ⊢ t = u :: A -> f t = g u :: B{t}
      Assumes that B{t} ≡ B{u} for this to make sense! *)
| Inject of proof * pconstructor * int * int
  (** ⊢ ci v = ci w :: Ind(args) -> ⊢ v = w :: T
      where T is the type of the n-th argument of ci, assuming they coincide *)
and proof =
    private {p_lhs:ATerm.t;p_rhs:ATerm.t;p_rule:rule}

(** Main proof building function *)

val build_proof :
  Environ.env -> Evd.evar_map -> forest ->
  [ `Discr of int * pa_constructor * int * pa_constructor
  | `Prove of int * int ] -> proof

