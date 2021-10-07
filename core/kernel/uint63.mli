(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t

val uint_size : int
val maxuint31 : t

      (* conversion to int *)
val of_int : int -> t
val to_int2 : t -> int * int (* msb, lsb *)
val of_int64 : Int64.t -> t
val to_int64 : t -> Int64.t
(*
val of_uint : int -> t
 *)
(** [int_min n m] returns the minimum of [n] and [m],
    [m] must be in [0, 2^30-1]. *)
val to_int_min : t -> int -> int

      (* conversion to float *)
val of_float : float -> t
val to_float : t -> float

val hash : t -> int

     (* conversion to a string *)
val to_string : t -> string

val compile : t -> string

(* constants *)
val zero    : t
val one : t

      (* logical operations *)
val l_sl    : t -> t -> t
val l_sr    : t -> t -> t
val l_and   : t -> t -> t
val l_xor   : t -> t -> t
val l_or    : t -> t -> t

      (* Arithmetic operations *)
val a_sr    : t -> t -> t
val add     : t -> t -> t
val sub     : t -> t -> t
val mul     : t -> t -> t
val div     : t -> t -> t
val rem     : t -> t -> t

val diveucl : t -> t -> t * t

      (* Signed arithmetic opeartions *)
val divs     : t -> t -> t
val rems     : t -> t -> t

      (* Specific arithmetic operations *)
val mulc    : t -> t -> t * t
val addmuldiv : t -> t -> t -> t

(** [div21 xh xl y] returns [q % 2^63, r]
    s.t. [xh * 2^63 + xl = q * y + r] and [r < y].
    When [y] is [0], returns [0, 0]. *)
val div21   : t -> t -> t -> t * t

      (* comparison *)
val lt      : t -> t -> bool
val equal      : t -> t -> bool
val le      : t -> t -> bool
val compare : t -> t -> int

      (* signed comparision *)
val lts      : t -> t -> bool
val les      : t -> t -> bool
val compares : t -> t -> int

      (* head and tail *)
val head0   : t -> t
val tail0   : t -> t

val is_uint63 : Obj.t -> bool

(* Arithmetic with explicit carries *)

(* Analog of Numbers.Abstract.Cyclic.carry *)
type 'a carry = C0 of 'a | C1 of 'a

val addc : t -> t -> t carry
val addcarryc : t -> t -> t carry
val subc : t -> t -> t carry
val subcarryc : t -> t -> t carry
