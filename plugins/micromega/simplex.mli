(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Polynomial
open Mutils
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
(*type solution = InfVect.Inf.t Int.Map.t

val find_point : cstr list -> solution option *)
val find_unsat_certificate : cstr list -> Vect.t option

val integer_solver :
  ISet.t option -> WithProof.t list -> ProofFormat.proof option
