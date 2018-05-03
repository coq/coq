(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type var = int

module Monomial : sig

  type t
  val fold : (var -> int -> 'a -> 'a) -> t -> 'a -> 'a
  val const : t
  val sqrt : t -> t option
  val is_var : t -> bool
  val div : t -> t -> t * int

  val compare : t -> t -> int

end

module Poly : sig

  type t

  val constant : Num.num -> t
  val variable : var -> t
  val addition : t -> t -> t
  val product : t -> t -> t
  val uminus : t -> t
  val get : Monomial.t -> t -> Num.num
  val fold : (Monomial.t -> Num.num -> 'a -> 'a) -> t -> 'a -> 'a

  val is_linear : t -> bool

  val add : Monomial.t -> Num.num -> t -> t

end

module Vect : sig

  type var = int
  type t = (var * Num.num) list
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp_vect : 'a -> t -> unit

  val get : var -> t -> Num.num option
  val set : var -> Num.num -> t -> t
  val fresh : (int * 'a) list -> int
  val update : Int.t -> (Num.num -> Num.num) ->
    (Int.t * Num.num) list -> (Int.t * Num.num) list
  val null : t

  val from_list : Num.num list -> t
  val to_list : t -> Num.num list

  val add : t -> t -> t
  val mul : Num.num -> t -> t

end

type cstr_compat = {coeffs : Vect.t ; op : op ; cst : Num.num}
and op = Eq | Ge

type prf_rule =
  | Hyp of int
  | Def of int
  | Cst  of Big_int.big_int
  | Zero
  | Square of (Vect.t * Num.num)
  | MulC of (Vect.t * Num.num) * prf_rule
  | Gcd of Big_int.big_int * prf_rule
  | MulPrf of prf_rule * prf_rule
  | AddPrf of prf_rule * prf_rule
  | CutPrf of prf_rule

type proof =
  | Done
  | Step of int * prf_rule * proof
  | Enum of int * prf_rule * Vect.t * prf_rule * proof list

val proof_max_id : proof -> int

val normalise_proof : int -> proof -> int * proof

val output_proof : out_channel -> proof -> unit

val add_proof : prf_rule -> prf_rule -> prf_rule
val mul_proof : Big_int.big_int -> prf_rule -> prf_rule

module LinPoly : sig

  type t = Vect.t * Num.num

  module MonT : sig

    val clear : unit -> unit
    val retrieve : int -> Monomial.t

  end

  val pivot_eq : Vect.var ->
           cstr_compat * prf_rule ->
           cstr_compat * prf_rule -> (cstr_compat * prf_rule) option

  val linpol_of_pol : Poly.t -> t

end

val output_cstr : out_channel -> cstr_compat -> unit

val opMult : op -> op -> op
