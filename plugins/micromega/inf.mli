(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open NumCompat

(** a + b.e where a and b are rationals and e > 0  *)
type t

(** [set_tolerance ()] set a rational used to concretise e.
    (This is used to get a fractional part in Q.t)
 *)
val set_tolerance : Q.t -> unit

(** [decomp (a + b.e)] returns  [(a,b)] *)
val decomp :  t -> Q.t * Q.t

(** [cst q] returns q + 0.e *)
val cst : Q.t -> t

(** [zero] is (0 + 0.e) *)
val zero : t

(** [epsilon] is (0 + 1.e) *)
val epsilon : t

(** [cste c strict] = if strict then c - 1.e else c + 0.e *)
val cste : Q.t -> bool -> t

(** [hash x] returns a hash *)
val hash : t -> int

(** [add (a1+b1.e) (a2+b2.e)] returns a1+a2 + (b1_b2).e *)
val add : t -> t -> t

(** [mulc c (a+b.e)] returns c*a + c*b.e *)
val mulc : Q.t -> t -> t

(** [divc (a+b.e) c] returns a/c + b/c.e *)
val divc : t -> Q.t -> t

(** [uminus (a+b.e)] returns -a + -b.e *)
val uminus : t -> t

(** [lt (a1+b1.e) (a2+b2.e)] returns a1 < a2 \/ a1 = a2 /\ b1 < b2 *)
val lt : t -> t -> bool

(** [abs (a+b.e)] returns (a+b.e) < 0 then (-a-b.e) else (a+b.e) *)
val abs : t -> t

(** [ge_0 (a1+b1.e)] compares with (0+0.e) *)
val  ge_0 : t -> bool

(** [equal (a1+b1.e) (a2+b2.e)] holds iff a1 = a2 /\ b1 = b2 *)
val equal : t -> t -> bool

(** [compare] provides a total ordering *)
val compare : t -> t -> int

(** [pp o (a1+b1.e)] outputs on out_channel [o] a textual representation *)
val pp : out_channel -> t -> unit

(** [pp_smt  o (a1+b1.e)] outputs on out_channel [o] a smt-lib textual representation *)
val pp_smt : out_channel -> t -> unit


(** [is_zero (a+b.e)] holds if a = b = 0 *)
val is_zero : t -> bool

(** [gcd (a/a'+b/b'.e)] returns the gcd(a,b) *)
val gcd : t -> Z.t

(** [ppcm (a/a'+b/b'.e)] returns ppcm(a',b') *)
val ppcm : t -> Z.t

(** [frac_num a+b.e] returns the fractional part of a+b.e *)
val frac_num : t -> Q.t option
