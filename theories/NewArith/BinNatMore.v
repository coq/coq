Require Import NArith.
Require Import BinPosMore.
Require Import Prelude.

Open Scope N_scope.

Definition Nrect
  (P : N -> Type) (a : P 0)
    (f : forall n : N, P n -> P (Nsucc n)) (n : N) : P n :=
let f' (p : positive) (x : P (Npos p)) := f (Npos p) x in
let P' (p : positive) := P (Npos p) in
match n return (P n) with
| 0 => a
| Npos p => Prect P' (f 0 a) f' p
end.

Theorem Nrect_base : forall P a f, Nrect P a f 0 = a.
Proof.
intros P a f; simpl; reflexivity.
Qed.

Theorem Nrect_step : forall P a f n, Nrect P a f (Nsucc n) = f n (Nrect P a f n).
Proof.
intros P a f; destruct n as [| p]; simpl;
[rewrite Prect_base | rewrite Prect_succ]; reflexivity.
Qed.

Definition Nrec (P : N -> Set) := Nrect P.

Theorem Nrec_base : forall P a f, Nrec P a f 0 = a.
Proof.
intros P a f; unfold Nrec; apply Nrect_base.
Qed.

Theorem Nrec_step : forall P a f n, Nrec P a f (Nsucc n) = f n (Nrec P a f n).
Proof.
intros P a f; unfold Nrec; apply Nrect_step.
Qed.

Definition Nind (P : N -> Prop) := Nrect P. (* Should replace of BinNat.Nind *)

Theorem Ntimes_Sn_m : forall n m : N, (Nsucc n) * m = m + n * m.
Proof.
destruct n as [| n]; destruct m as [| m]; simpl; auto.
rewrite Ptimes_Sn_m; reflexivity.
Qed.

Theorem noteq_Sn_0 : forall n : N, Nsucc n <> 0.
Proof.
intro n; elim n; simpl Nsucc; intros; discriminate.
Qed.

Theorem Ncompare_n_0 : forall n : N, Ncompare n 0 <> Lt.
Proof.
destruct n; discriminate.
Qed.

Theorem Ncompare_n_Sm :
  forall n m : N, Ncompare n (Nsucc m) = Lt <-> Ncompare n m = Lt \/ n = m.
Proof.
intros n m; split; destruct n as [| p]; destruct m as [| q]; simpl; auto.
destruct p; simpl; intros; discriminate.
pose proof (proj1 (Pcompare_p_Sq p q));
assert (p = q <-> Npos p = Npos q); [split; congruence | tauto].
intros H; destruct H; discriminate.
pose proof (proj2 (Pcompare_p_Sq p q));
assert (p = q <-> Npos p = Npos q); [split; congruence | tauto].
Qed.

Close Scope N_scope.
