(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

include Float64_common

let mul (x : float) (y : float) : float = x *. y
[@@ocaml.inline always]

let add (x : float) (y : float) : float = x +. y
[@@ocaml.inline always]

let sub (x : float) (y : float) : float = x -. y
[@@ocaml.inline always]

let div (x : float) (y : float) : float = x /. y
[@@ocaml.inline always]

let sqrt (x : float) : float = sqrt x
[@@ocaml.inline always]

(*** Test at runtime that no harmful double rounding seems to
   be performed with an intermediate 80 bits representation (x87). *)
let () =
  let b = ldexp 1. 53 in
  let s = add 1. (ldexp 1. (-52)) in
  if add b s <= b || add b 1. <> b || ldexp 1. (-1074) <= 0. then
    failwith "Detected non IEEE-754 compliant architecture (or wrong \
              rounding mode). Use of Float is thus unsafe."
