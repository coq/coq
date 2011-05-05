(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinNat.

(** Obsolete file, see [BinNat] now,
    only compatibility notations remain here. *)

Notation Nsqrtrem := N.sqrtrem (only parsing).
Notation Nsqrt := N.sqrt (only parsing).
Notation Nsqrtrem_spec := N.sqrtrem_spec (only parsing).
Notation Nsqrt_spec := (fun n => N.sqrt_spec n (N.le_0_l n)) (only parsing).
Notation Nsqrtrem_sqrt := N.sqrtrem_sqrt (only parsing).
