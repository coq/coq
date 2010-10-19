(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Definition of a square root function for Z. *)

Require Import BinPos BinInt Psqrt.

Open Scope Z_scope.

Definition Zsqrtrem n :=
 match n with
  | 0 => (0, 0)
  | Zpos p =>
    match Psqrtrem p with
     | (s, IsPos r) => (Zpos s, Zpos r)
     | (s, _) => (Zpos s, 0)
    end
  | Zneg _ => (0,0)
 end.

Definition Zsqrt n :=
 match n with
  | 0 => 0
  | Zpos p => Zpos (Psqrt p)
  | Zneg _ => 0
 end.

Lemma Zsqrtrem_spec : forall n, 0<=n ->
 let (s,r) := Zsqrtrem n in n = s*s + r /\ 0 <= r <= 2*s.
Proof.
 destruct n. now repeat split.
 generalize (Psqrtrem_spec p). simpl.
 destruct 1; simpl; subst; now repeat split.
 now destruct 1.
Qed.

Lemma Zsqrt_spec : forall n, 0<=n ->
 let s := Zsqrt n in s*s <= n < (Zsucc s)*(Zsucc s).
Proof.
 destruct n. now repeat split. unfold Zsqrt.
 rewrite <- Zpos_succ_morphism. intros _. apply (Psqrt_spec p).
 now destruct 1.
Qed.

Lemma Zsqrt_neg : forall n, n<0 -> Zsqrt n = 0.
Proof.
 intros. now destruct n.
Qed.

Lemma Zsqrtrem_sqrt : forall n, fst (Zsqrtrem n) = Zsqrt n.
Proof.
 destruct n; try reflexivity.
 unfold Zsqrtrem, Zsqrt, Psqrt.
 destruct (Psqrtrem p) as (s,r). now destruct r.
Qed.