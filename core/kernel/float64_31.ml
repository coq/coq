(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

include Float64_common

external mul : float -> float -> float = "coq_fmul_byte" "coq_fmul"
[@@unboxed] [@@noalloc]

external add : float -> float -> float = "coq_fadd_byte" "coq_fadd"
[@@unboxed] [@@noalloc]

external sub : float -> float -> float = "coq_fsub_byte" "coq_fsub"
[@@unboxed] [@@noalloc]

external div : float -> float -> float = "coq_fdiv_byte" "coq_fdiv"
[@@unboxed] [@@noalloc]

external sqrt : float -> float = "coq_fsqrt_byte" "coq_fsqrt"
[@@unboxed] [@@noalloc]

(*** Test at runtime that no harmful double rounding seems to
   be performed with an intermediate 80 bits representation (x87). *)
let () =
  let b = ldexp 1. 53 in
  let s = add 1. (ldexp 1. (-52)) in
  if add b s <= b || add b 1. <> b || ldexp 1. (-1074) <= 0. then
    failwith "Detected non IEEE-754 compliant architecture (or wrong \
              rounding mode). Use of Float is thus unsafe."
