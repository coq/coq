(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Num

type interval = num option * num option
val pp : out_channel -> interval -> unit
val inter : interval -> interval -> interval option
val range : interval -> num option
val smaller_itv : interval -> interval -> bool
val in_bound : interval -> num -> bool
val norm_itv : interval -> interval option
