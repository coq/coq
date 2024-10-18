(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* OCaml's float type follows the IEEE 754 Binary64 (double precision)
   format *)
type t = float

(* The [f : float] type annotation enable the compiler to compile f <> f
   as comparison on floats rather than the polymorphic OCaml comparison
   which is much slower. *)
let is_nan (f : float) = f <> f
let is_infinity f = f = infinity
let is_neg_infinity f = f = neg_infinity

(* OCaml gives a sign to nan values which should not be displayed as
   all NaNs are considered equal here.
   OCaml prints infinities as "inf" (resp. "-inf")
   but we want "infinity" (resp. "neg_infinity"). *)
let to_string_raw fmt f =
  if is_nan f then "nan"
  else if is_infinity f then "infinity"
  else if is_neg_infinity f then "neg_infinity"
  else Printf.sprintf fmt f

let to_hex_string = to_string_raw "%h"

(* Printing a binary64 float in 17 decimal places and parsing it again
   will yield the same float. *)
let to_string = to_string_raw "%.17g"

let of_string = float_of_string

(* Compiles a float to OCaml code *)
let compile f =
  Printf.sprintf "Float64.of_float (%s)" (to_hex_string f)

let of_float f = f

let to_float f = if is_nan f then nan else f

let sign f = copysign 1. f < 0.

let opp = ( ~-. )
let abs = abs_float

type float_comparison = FEq | FLt | FGt | FNotComparable

(* See above comment on [is_nan] for the [float] type annotations. *)
let eq (x : float) (y : float) = x = y
[@@ocaml.inline always]

let lt (x : float) (y : float) = x < y
[@@ocaml.inline always]

let le (x : float) (y : float) = x <= y
[@@ocaml.inline always]

(* inspired by lib/util.ml; see also #10471 *)
let pervasives_compare (x : float) (y : float) = compare x y

let compare (x : float) (y : float) =
  if x < y then FLt
  else
  (
    if x > y then FGt
    else
    (
      if x = y then FEq
      else FNotComparable (* NaN case *)
    )
  )
[@@ocaml.inline always]

type float_class =
  | PNormal | NNormal | PSubn | NSubn | PZero | NZero | PInf | NInf | NaN

let classify x =
  match classify_float x with
  | FP_normal -> if 0. < x then PNormal else NNormal
  | FP_subnormal -> if 0. < x then PSubn else NSubn
  | FP_zero -> if 0. < 1. /. x then PZero else NZero
  | FP_infinite -> if 0. < x then PInf else NInf
  | FP_nan -> NaN
[@@ocaml.inline always]

let of_uint63 x = Uint63.to_float x
[@@ocaml.inline always]

let prec = 53
let normfr_mantissa f =
  let f = abs f in
  if f >= 0.5 && f < 1. then Uint63.of_float (ldexp f prec)
  else Uint63.zero
[@@ocaml.inline always]

let eshift = 2101 (* 2*emax + prec *)

(* When calling frexp on a nan or an infinity, the returned value inside
   the exponent is undefined.
   Therefore we must always set it to a fixed value (here 0). *)
let frshiftexp f =
  match classify_float f with
  | FP_zero | FP_infinite | FP_nan -> (f, Uint63.zero)
  | FP_normal | FP_subnormal ->
    let (m, e) = frexp f in
    m, Uint63.of_int (e + eshift)
[@@ocaml.inline always]

let ldshiftexp f e = ldexp f (Uint63.to_int_min e (2 * eshift) - eshift)
[@@ocaml.inline always]

external next_up : float -> float = "rocq_next_up_byte" "rocq_next_up"
[@@unboxed] [@@noalloc]

external next_down : float -> float = "rocq_next_down_byte" "rocq_next_down"
[@@unboxed] [@@noalloc]

let equal f1 f2 =
  if f1 = f2 then f1 <> 0. || sign f1 = sign f2 (* OCaml consider 0. = -0. *)
  else is_nan f1 && is_nan f2
[@@ocaml.inline always]

let hash =
  (* Hashtbl.hash already considers all NaNs as equal,
     cf. https://github.com/ocaml/ocaml/commit/aea227fdebe0b5361fd3e1d0aaa42cf929052269
     and http://caml.inria.fr/pub/docs/manual-ocaml/libref/Hashtbl.html *)
  Hashtbl.hash

let total_compare f1 f2 =
  (* pervasives_compare considers all NaNs as equal, which is fine here,
     but also considers -0. and +0. as equal *)
  if f1 = 0. && f2 = 0. then pervasives_compare (1. /. f1) (1. /. f2)
  else pervasives_compare f1 f2

let is_float64 t =
  Obj.tag t = Obj.double_tag
[@@ocaml.inline always]
