(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ccalgo
open EConstr

type rule=
    Ax of (Evd.evar_map*constr)
  | SymAx of (Evd.evar_map*constr)
  | Refl of term
  | Trans of proof*proof
  | Congr of proof*proof
  | Inject of proof*(Names.constructor*EInstance.t)*int*int
and proof =
    private {p_lhs:term;p_rhs:term;p_rule:rule}

(** Proof smart constructors *)

val prefl:term -> proof

val pcongr: proof -> proof -> proof

val ptrans: proof -> proof -> proof

val psym: proof -> proof

val pax : (Ccalgo.term * Ccalgo.term) Ccalgo.Constrhash.t ->
           Ccalgo.Constrhash.key -> proof

val psymax :  (Ccalgo.term * Ccalgo.term) Ccalgo.Constrhash.t ->
           Ccalgo.Constrhash.key -> proof

val pinject :  proof -> (Names.constructor * EInstance.t) -> int -> int -> proof

(** Proof building functions *)

val equal_proof : forest -> int -> int -> proof

val edge_proof : forest -> (int*int)*equality -> proof

val path_proof : forest -> int -> ((int*int)*equality) list -> proof

val congr_proof :  forest -> int -> int -> proof

val ind_proof : forest -> int -> pa_constructor -> int -> pa_constructor -> proof

(** Main proof building function *)

val build_proof :
  forest ->
  [ `Discr of int * pa_constructor * int * pa_constructor
  | `Prove of int * int ] -> proof

