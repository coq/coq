(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* OCaml's float type follows the IEEE 754 Binary64 (double precision)
   format *)
type t = float

let is_nan f = f <> f

(* OCaml give a sign to nan values which should not be displayed as all nan are
 * considered equal *)
let to_string f = if is_nan f then "nan" else string_of_float f
let of_string = float_of_string

let of_float f = f

let opp = ( ~-. )
let abs = abs_float

type float_comparison = FEq | FLt | FGt | FNotComparable

let compare x y =
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

type float_class =
  | PNormal | NNormal | PSubn | NSubn | PZero | NZero | PInf | NInf | NaN

let classify x =
  match classify_float x with
  | FP_normal -> if 0. < x then PNormal else NNormal
  | FP_subnormal -> if 0. < x then PSubn else NSubn
  | FP_zero -> if 0. < 1. /. x then PZero else NZero
  | FP_infinite -> if 0. < x then PInf else NInf
  | FP_nan -> NaN

let mul = ( *. )
let add = ( +. )
let sub = ( -. )
let div = ( /. )
let sqrt = sqrt

let of_int63 = Uint63.to_float
let prec = 53
let normfr_mantissa f =
  let f = abs f in
  if f >= 0.5 && f < 1. then Uint63.of_float (ldexp f prec)
  else Uint63.zero

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

let ldshiftexp f e = ldexp f (snd (Uint63.to_int2 e) - eshift)

let equal f1 f2 =
  match classify_float f1 with
  | FP_normal | FP_subnormal | FP_infinite -> (f1 = f2)
  | FP_nan -> is_nan f2
  | FP_zero -> f1 = f2 && 1. /. f1 = 1. /. f2 (* OCaml consider 0. = -0. *)

let hash =
  (* Hashtbl.hash already considers all NaNs as equal,
     cf. https://github.com/ocaml/ocaml/commit/aea227fdebe0b5361fd3e1d0aaa42cf929052269
     and http://caml.inria.fr/pub/docs/manual-ocaml/libref/Hashtbl.html *)
  Hashtbl.hash

let total_compare f1 f2 =
  (* pervasives_compare considers all NaNs as equal, which is fine here,
     but also considers -0. and +0. as equal *)
  if f1 = 0. && f2 = 0. then Util.pervasives_compare (1. /. f1) (1. /. f2)
  else Util.pervasives_compare f1 f2
