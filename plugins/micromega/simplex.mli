(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Polynomial

val optimise : Vect.t -> cstr list -> (Num.num option * Num.num option) option

val find_point : cstr list -> Vect.t option

val find_unsat_certificate : cstr list -> Vect.t option

val integer_solver : (cstr * ProofFormat.prf_rule) list -> ProofFormat.proof option
