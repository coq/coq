(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module IMap : CSig.MapS with type key = int

type proof

module Fourier : sig


  val find_point : Polynomial.cstr list ->
    (Vect.t, proof) Util.union

  val optimise : Vect.t ->
    Polynomial.cstr list ->
    Itv.interval option

end

val pp_proof : out_channel -> proof -> unit

module Proof : sig

  val mk_proof : Polynomial.cstr list ->
    proof -> (Vect.t * Polynomial.cstr) list

  val add_op : Polynomial.op -> Polynomial.op -> Polynomial.op

end

exception TimeOut
