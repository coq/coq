(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinNat.

(** Obsolete file, see [BinNat] now,
    only compatibility notations remain here. *)

Notation Nsqrt_spec := (fun n => N.sqrt_spec n (N.le_0_l n)) (only parsing).
