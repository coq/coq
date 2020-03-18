(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open NumCompat
open Polynomial

(** Profiling *)

type profile_info =
  { number_of_successes : int
  ; number_of_failures : int
  ; success_pivots : int
  ; failure_pivots : int
  ; average_pivots : int
  ; maximum_pivots : int }

val get_profile_info : unit -> profile_info

(** Simplex interface *)

val optimise : Vect.t -> cstr list -> (Q.t option * Q.t option) option
val find_point : cstr list -> Vect.t option
val find_unsat_certificate : cstr list -> Vect.t option

val integer_solver :
  (cstr * ProofFormat.prf_rule) list -> ProofFormat.proof option
