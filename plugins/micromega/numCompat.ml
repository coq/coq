(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
  type t = Big_int.big_int

  open Big_int

  let zero = zero_big_int
  let one = unit_big_int
  let two = big_int_of_int 2
  let add = Big_int.add_big_int
  let sub = Big_int.sub_big_int
  let mul = Big_int.mult_big_int
  let div = Big_int.div_big_int
  let neg = Big_int.minus_big_int
  let sign = Big_int.sign_big_int
  let equal = eq_big_int
  let compare = compare_big_int
  let power_int = power_big_int_positive_int
  let quomod = quomod_big_int

  let ppcm x y =
    let g = gcd_big_int x y in
    let x' = div_big_int x g in
    let y' = div_big_int y g in
    mult_big_int g (mult_big_int x' y')

  let gcd = gcd_big_int

  let lcm x y =
    if eq_big_int x zero && eq_big_int y zero then zero
    else abs_big_int (div_big_int (mult_big_int x y) (gcd x y))

  let to_string = string_of_big_int
end

module type QArith = sig
  module Z : ZArith

  type t

  val of_int : int -> t
  val zero : t
  val one : t
  val two : t
  val ten : t
  val neg_one : t

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

  type t = Num.num

  open Num

  let of_int x = Int x
  let zero = Int 0
  let one = Int 1
  let two = Int 2
  let ten = Int 10
  let neg_one = Int (-1)

  module Notations = struct
    let ( // ) = div_num
    let ( +/ ) = add_num
    let ( -/ ) = sub_num
    let ( */ ) = mult_num
    let ( =/ ) = eq_num
    let ( <>/ ) = ( <>/ )
    let ( >/ ) = ( >/ )
    let ( >=/ ) = ( >=/ )
    let ( </ ) = ( </ )
    let ( <=/ ) = ( <=/ )
  end

  let compare = compare_num
  let make x y = Big_int x // Big_int y

  let numdom r =
    let r' = Ratio.normalize_ratio (ratio_of_num r) in
    (Ratio.numerator_ratio r', Ratio.denominator_ratio r')

  let num x = numdom x |> fst
  let den x = numdom x |> snd
  let of_bigint x = Big_int x
  let to_bigint = big_int_of_num
  let neg = minus_num

  (* let inv =  *)
  let max = max_num
  let min = min_num
  let sign = sign_num
  let abs = abs_num
  let mod_ = mod_num
  let floor = floor_num
  let ceiling = ceiling_num
  let round = round_num
  let pow2 n = power_num two (Int n)
  let pow10 n = power_num ten (Int n)
  let power x = power_num (Int x)
  let to_string = string_of_num
  let of_string = num_of_string
  let to_float = float_of_num
end
