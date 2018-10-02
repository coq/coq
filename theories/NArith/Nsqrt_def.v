(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinNat.

(** Obsolete file, see [BinNat] now,
    only compatibility notations remain here. *)

Notation Nsqrtrem := N.sqrtrem (compat "8.7").
Notation Nsqrt := N.sqrt (compat "8.7").
Notation Nsqrtrem_spec := N.sqrtrem_spec (compat "8.7").
Notation Nsqrt_spec := (fun n => N.sqrt_spec n (N.le_0_l n)) (only parsing).
Notation Nsqrtrem_sqrt := N.sqrtrem_sqrt (compat "8.7").
