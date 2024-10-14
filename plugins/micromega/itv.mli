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

type interval = Q.t option * Q.t option

val pp : out_channel -> interval -> unit
val inter : interval -> interval -> interval option
val range : interval -> Q.t option
val smaller_itv : interval -> interval -> bool
val in_bound : interval -> Q.t -> bool
val norm_itv : interval -> interval option
