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
let is_infinity f = f = infinity
let is_neg_infinity f = f = neg_infinity

(* Printing a binary64 float in 17 decimal places and parsing it again
   will yield the same float. We assume [to_string_raw] is not given a
   [nan] as input. *)
let to_string_raw f = Printf.sprintf "%.17g" f

(* OCaml gives a sign to nan values which should not be displayed as
   all NaNs are considered equal here *)
let to_string f = if is_nan f then "nan" else to_string_raw f
let of_string = float_of_string

(* Compiles a float to OCaml code *)
let compile f =
  let s =
    if is_nan f then "nan" else if is_neg_infinity f then "neg_infinity"
    else Printf.sprintf "%h" f in
  Printf.sprintf "Float64.of_float (%s)" s

let of_float f = f

let sign f = copysign 1. f < 0.

let opp = ( ~-. )
let abs = abs_float

type float_comparison = FEq | FLt | FGt | FNotComparable

(* inspired by lib/util.ml; see also #10471 *)
let pervasives_compare = compare

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

let mul x y = x *. y
[@@ocaml.inline always]

let add x y = x +. y
[@@ocaml.inline always]

let sub x y = x -. y
[@@ocaml.inline always]

let div x y = x /. y
[@@ocaml.inline always]

let sqrt x = sqrt x
[@@ocaml.inline always]

let of_int63 x = Uint63.to_float x
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

let ldshiftexp f e = ldexp f (snd (Uint63.to_int2 e) - eshift)
[@@ocaml.inline always]

let eta_float = ldexp 1. (-1074) (* smallest positive float (subnormal) *)

let next_up f =
  match classify_float f with
  | FP_nan -> f
  | FP_infinite -> if 0. < f then f else -.max_float
  | FP_zero | FP_subnormal ->
     let f = f +. eta_float in
     if f = 0. then -0. else f (* or next_down may return -0. *)
  | FP_normal ->
     let f, e = frexp f in
     if 0. < f || f <> -0.5 || e = -1021 then
       ldexp (f +. epsilon_float /. 2.) e
     else
       ldexp (-0.5 +. epsilon_float /. 4.) e
[@@ocaml.inline always]

let next_down f = -.(next_up (-.f))
[@@ocaml.inline always]

let equal f1 f2 =
  match classify_float f1 with
  | FP_normal | FP_subnormal | FP_infinite -> (f1 = f2)
  | FP_nan -> is_nan f2
  | FP_zero -> f1 = f2 && 1. /. f1 = 1. /. f2 (* OCaml consider 0. = -0. *)
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
