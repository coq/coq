(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type ZArith = sig
  type t

  val zero : t
  val one : t
  val two : t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val neg : t -> t
  val sign : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val power_int : t -> int -> t
  val quomod : t -> t -> t * t
  val ppcm : t -> t -> t
  val gcd : t -> t -> t
  val lcm : t -> t -> t
  val to_string : t -> string
end

module Z = struct
  (* Beware this only works fine in ZArith >= 1.10 due to
     https://github.com/ocaml/Zarith/issues/58 *)
  include Z

  (* Constants *)
  let two = Z.of_int 2
  let ten = Z.of_int 10
  let power_int = Big_int_Z.power_big_int_positive_int
  let quomod = Big_int_Z.quomod_big_int

  (* zarith fails with division by zero if x == 0 && y == 0 *)
  let lcm x y = if Z.equal x zero && Z.equal y zero then zero else Z.lcm x y

  let ppcm x y =
    let g = gcd x y in
    let x' = Z.div x g in
    let y' = Z.div y g in
    Z.mul g (Z.mul x' y')
end

module type QArith = sig
  module Z : ZArith

  type t

  val of_int : int -> t
  val zero : t
  val one : t
  val two : t
  val ten : t
  val minus_one : t

  module Notations : sig
    val ( // ) : t -> t -> t
    val ( +/ ) : t -> t -> t
    val ( -/ ) : t -> t -> t
    val ( */ ) : t -> t -> t
    val ( =/ ) : t -> t -> bool
    val ( <>/ ) : t -> t -> bool
    val ( >/ ) : t -> t -> bool
    val ( >=/ ) : t -> t -> bool
    val ( </ ) : t -> t -> bool
    val ( <=/ ) : t -> t -> bool
  end

  val compare : t -> t -> int
  val make : Z.t -> Z.t -> t
  val den : t -> Z.t
  val num : t -> Z.t
  val of_bigint : Z.t -> t
  val to_bigint : t -> Z.t
  val neg : t -> t

  (* val inv : t -> t *)
  val max : t -> t -> t
  val min : t -> t -> t
  val sign : t -> int
  val abs : t -> t
  val mod_ : t -> t -> t
  val floor : t -> t

  (* val floorZ : t -> Z.t *)
  val ceiling : t -> t
  val round : t -> t
  val pow2 : int -> t
  val pow10 : int -> t
  val power : int -> t -> t
  val to_string : t -> string
  val of_string : string -> t
  val to_float : t -> float
end

module Q : QArith with module Z = Z = struct
  module Z = Z

  let pow_check_exp x y =
    let z_res =
      if y = 0 then Z.one
      else if y > 0 then Z.pow x y
      else (* s < 0 *)
        Z.pow x (abs y)
    in
    let z_res = Q.of_bigint z_res in
    if 0 <= y then z_res else Q.inv z_res

  include Q

  let two = Q.(of_int 2)
  let ten = Q.(of_int 10)

  module Notations = struct
    let ( // ) = Q.div
    let ( +/ ) = Q.add
    let ( -/ ) = Q.sub
    let ( */ ) = Q.mul
    let ( =/ ) = Q.equal
    let ( <>/ ) x y = not (Q.equal x y)
    let ( >/ ) = Q.gt
    let ( >=/ ) = Q.geq
    let ( </ ) = Q.lt
    let ( <=/ ) = Q.leq
  end

  (* XXX: review / improve *)
  let floorZ q : Z.t = Z.fdiv (num q) (den q)
  let floor q : t = floorZ q |> Q.of_bigint
  let ceiling q : t = Z.cdiv (Q.num q) (Q.den q) |> Q.of_bigint
  let half = Q.make Z.one Z.two

  (* We imitate Num's round which is to the nearest *)
  let round q = floor (Q.add half q)

  (* XXX: review / improve *)
  let quo x y =
    let s = sign y in
    let res = floor (x / abs y) in
    if Int.equal s (-1) then neg res else res

  let mod_ x y = x - (y * quo x y)

  (* XXX: review / improve *)
  (* Note that Z.pow doesn't support negative exponents *)

  let pow2 y = pow_check_exp Z.two y
  let pow10 y = pow_check_exp Z.ten y

  let power (x : int) (y : t) : t =
    let y =
      try Q.to_int y
      with Z.Overflow ->
        (* XXX: make doesn't link Pp / CErrors for csdpcert, that could be fixed *)
        raise (Invalid_argument "[micromega] overflow in exponentiation")
      (* CErrors.user_err (Pp.str "[micromega] overflow in exponentiation") *)
    in
    pow_check_exp (Z.of_int x) y
end
