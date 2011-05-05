(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Definition of a square root function for N. *)

Require Import BinPos BinNat.

Local Open Scope N_scope.

Definition Nsqrtrem n :=
 match n with
  | N0 => (N0, N0)
  | Npos p =>
    match Pos.sqrtrem p with
     | (s, IsPos r) => (Npos s, Npos r)
     | (s, _) => (Npos s, N0)
    end
 end.

Definition Nsqrt n :=
 match n with
  | N0 => N0
  | Npos p => Npos (Pos.sqrt p)
 end.

Lemma Nsqrtrem_spec : forall n,
 let (s,r) := Nsqrtrem n in n = s*s + r /\ r <= 2*s.
Proof.
 destruct n. now split.
 generalize (Pos.sqrtrem_spec p). simpl.
 destruct 1; simpl; subst; now split.
Qed.

Lemma Nsqrt_spec : forall n,
 let s := Nsqrt n in s*s <= n < (Nsucc s)*(Nsucc s).
Proof.
 destruct n. now split. apply (Pos.sqrt_spec p).
Qed.

Lemma Nsqrtrem_sqrt : forall n, fst (Nsqrtrem n) = Nsqrt n.
Proof.
 destruct n. reflexivity.
 unfold Nsqrtrem, Nsqrt, Pos.sqrt.
 destruct (Pos.sqrtrem p) as (s,r). now destruct r.
Qed.