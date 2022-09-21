(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ccalgo
open Constr

type rule=
    Ax of constr
  | SymAx of constr
  | Refl of ATerm.t
  | Trans of proof*proof
  | Congr of proof*proof
  | Inject of proof*pconstructor*int*int
and proof =
    private {p_lhs:ATerm.t;p_rhs:ATerm.t;p_rule:rule}

(** Main proof building function *)

val build_proof :
  Environ.env -> Evd.evar_map -> forest ->
  [ `Discr of int * pa_constructor * int * pa_constructor
  | `Prove of int * int ] -> proof

