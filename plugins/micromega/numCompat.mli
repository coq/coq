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

  (** [gcd x y] Greatest Common Divisor. Must always return a
     positive number *)
  val gcd : t -> t -> t

  (** [lcm x y] Least Common Multiplier. Must always return a
     positive number *)
  val lcm : t -> t -> t

  val to_string : t -> string
end

module type QArith = sig
  module Z : ZArith

  type t

  val of_int : int -> t
  val zero : t
  val one : t
  val two : t
  val ten : t

  (** -1 constant  *)
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
  val ceiling : t -> t
  val round : t -> t
  val pow2 : int -> t
  val pow10 : int -> t
  val power : int -> t -> t
  val to_string : t -> string
  val of_string : string -> t
  val to_float : t -> float
end

module Z : ZArith
module Q : QArith with module Z = Z
