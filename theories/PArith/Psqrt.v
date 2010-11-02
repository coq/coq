(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos.

Open Scope positive_scope.

Definition Pleb x y :=
 match Pcompare x y Eq with Gt => false | _ => true end.

(** A Square Root function for positive numbers *)

(** We procede by blocks of two digits : if p is written qbb'
    then sqrt(p) will be sqrt(q)~0 or sqrt(q)~1.
    For deciding easily in which case we are, we store the remainder
    (as a positive_mask, since it can be null).
    Instead of copy-pasting the following code four times, we
    factorize as an auxiliary function, with f and g being either
    xO or xI depending of the initial digits.
    NB: (Pminus_mask (g (f 1)) 4) is a hack, morally it's g (f 0).
*)

Definition Psqrtrem_step (f g:positive->positive) p :=
 match p with
  | (s, IsPos r) =>
    let s' := s~0~1 in
    let r' := g (f r) in
    if Pleb s' r' then (s~1, Pminus_mask r' s')
    else (s~0, IsPos r')
  | (s,_)  => (s~0, Pminus_mask (g (f 1)) 4)
 end.

Fixpoint Psqrtrem p : positive * positive_mask :=
 match p with
  | 1 => (1,IsNul)
  | 2 => (1,IsPos 1)
  | 3 => (1,IsPos 2)
  | p~0~0 => Psqrtrem_step xO xO (Psqrtrem p)
  | p~0~1 => Psqrtrem_step xO xI (Psqrtrem p)
  | p~1~0 => Psqrtrem_step xI xO (Psqrtrem p)
  | p~1~1 => Psqrtrem_step xI xI (Psqrtrem p)
 end.

Definition Psqrt p := fst (Psqrtrem p).

(** An inductive relation for specifying sqrt results *)

Inductive PSQRT : positive*positive_mask -> positive -> Prop :=
 | PSQRT_exact : forall s x, x=s*s -> PSQRT (s,IsNul) x
 | PSQRT_approx : forall s r x, x=s*s+r -> r <= s~0 -> PSQRT (s,IsPos r) x.

(** Correctness proofs *)

Lemma Psqrtrem_step_spec : forall f g p x,
 (f=xO \/ f=xI) -> (g=xO \/ g=xI) ->
 PSQRT p x -> PSQRT (Psqrtrem_step f g p) (g (f x)).
Proof.
intros f g _ _ Hf Hg [ s _ -> | s r _ -> Hr ].
(* exact *)
unfold Psqrtrem_step.
destruct Hf,Hg; subst; simpl Pminus_mask;
 constructor; try discriminate; now rewrite Psquare_xO.
(* approx *)
assert (Hfg : forall p q, g (f (p+q)) = p~0~0 + g (f q))
 by (intros; destruct Hf, Hg; now subst).
unfold Psqrtrem_step. unfold Pleb.
case Pcompare_spec; [intros EQ | intros LT | intros GT].
(* - EQ *)
rewrite <- EQ. rewrite Pminus_mask_diag.
destruct Hg; subst g; try discriminate.
destruct Hf; subst f; try discriminate.
injection EQ; clear EQ; intros <-.
constructor. now rewrite Psquare_xI.
(* - LT *)
destruct (Pminus_mask_Gt (g (f r)) (s~0~1)) as (y & -> & H & _).
change Eq with (CompOpp Eq). now rewrite <- Pcompare_antisym, LT.
constructor.
rewrite Hfg, <- H. now rewrite Psquare_xI, Pplus_assoc.
apply Ple_lteq, Pcompare_p_Sq in Hr; change (r < s~1) in Hr.
apply Ple_lteq, Pcompare_p_Sq; change (y < s~1~1).
apply Pplus_lt_mono_l with (s~0~1).
rewrite H. simpl. rewrite Pplus_carry_spec, Pplus_diag. simpl.
set (s1:=s~1) in *; clearbody s1.
destruct Hf,Hg; subst; red; simpl;
  apply Hr || apply Pcompare_eq_Lt, Hr.
(* - GT *)
constructor.
rewrite Hfg. now rewrite Psquare_xO.
apply Ple_lteq, Pcompare_p_Sq, GT.
Qed.

Lemma Psqrtrem_spec : forall p, PSQRT (Psqrtrem p) p.
Proof.
fix 1.
 destruct p; try destruct p; try (constructor; easy);
  apply Psqrtrem_step_spec; auto.
Qed.

Lemma Psqrt_spec : forall p,
 let s := Psqrt p in s*s <= p < (Psucc s)*(Psucc s).
Proof.
 intros p. simpl.
 assert (H:=Psqrtrem_spec p).
 unfold Psqrt in *. destruct Psqrtrem as (s,rm); simpl.
 inversion_clear H; subst.
 (* exact *)
 split. red. rewrite Pcompare_refl. discriminate.
  apply Pmult_lt_mono; apply Pcompare_p_Sp.
 (* approx *)
 split.
 apply Ple_lteq; left. apply Plt_plus_r.
 rewrite (Pplus_one_succ_l).
 rewrite Pmult_plus_distr_r, !Pmult_plus_distr_l.
 rewrite !Pmult_1_r. simpl (1*s).
 rewrite <- Pplus_assoc, (Pplus_assoc s s), Pplus_diag, Pplus_assoc.
 rewrite (Pplus_comm (_+_)). apply Pplus_lt_mono_l.
 rewrite <- Pplus_one_succ_l. now apply Pcompare_p_Sq, Ple_lteq.
Qed.
