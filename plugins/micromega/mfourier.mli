(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Itv : sig

  type interval = Num.num option * Num.num option
  val range : interval -> Num.num option
  val smaller_itv : interval -> interval -> bool

end

module IMap : CSig.MapS with type key = int

type proof

module Fourier : sig

  val find_point : Polynomial.cstr_compat list ->
    ((IMap.key * Num.num) list, proof) Util.union

  val optimise : Polynomial.Vect.t ->
    Polynomial.cstr_compat list ->
    Itv.interval option

end

val pp_proof : out_channel -> proof -> unit

module Proof : sig

  val mk_proof : Polynomial.cstr_compat list ->
    proof -> (Polynomial.Vect.t * Polynomial.cstr_compat) list

  val add_op : Polynomial.op -> Polynomial.op -> Polynomial.op

end

val max_nb_cstr : int ref

val eval_op : Polynomial.op -> Num.num -> Num.num -> bool

exception TimeOut
