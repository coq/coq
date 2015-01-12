(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinNat.

(** Obsolete file, see [BinNat] now,
    only compatibility notations remain here. *)

Notation Nsqrtrem := N.sqrtrem (compat "8.3").
Notation Nsqrt := N.sqrt (compat "8.3").
Notation Nsqrtrem_spec := N.sqrtrem_spec (compat "8.3").
Notation Nsqrt_spec := (fun n => N.sqrt_spec n (N.le_0_l n)) (compat "8.3").
Notation Nsqrtrem_sqrt := N.sqrtrem_sqrt (compat "8.3").
