
(* $Id$ *)

(**************************************************************************)
(*                    Equality on natural numbers                         *)
(**************************************************************************)

Fixpoint  eq_nat [n:nat] : nat -> Prop :=
  [m:nat]Cases n m of 
                O      O     => True
             |  O     (S _)  => False
             | (S _)   O     => False
             | (S n1) (S m1) => (eq_nat n1 m1)
          end.

Theorem eq_nat_refl : (n:nat)(eq_nat n n).
Induction n; Simpl; Auto.
Qed.
Hints Resolve eq_nat_refl : arith v62.

Theorem eq_eq_nat : (n,m:nat)(n=m)->(eq_nat n m).
Induction 1; Trivial with arith.
Qed.
Hints Immediate eq_eq_nat : arith v62.

Theorem eq_nat_eq : (n,m:nat)(eq_nat n m)->(n=m).
Induction n; Induction m; Simpl; '(Contradiction Orelse Auto with arith).
Qed.
Hints Immediate eq_nat_eq : arith v62.

Theorem eq_nat_elim : (n:nat)(P:nat->Prop)(P n)->(m:nat)(eq_nat n m)->(P m).
Intros; Replace m with n; Auto with arith.
Qed.

Theorem eq_nat_decide : (n,m:nat){(eq_nat n m)}+{~(eq_nat n m)}.
Induction n.
Destruct m.
Auto with arith.
Intro; Right; Red; Trivial with arith.
Destruct m.
Right; Red; Auto with arith.
Intros.
Simpl.
Apply H.
Defined.

Fixpoint  beq_nat [n:nat] : nat -> bool :=
  [m:nat]Cases n m of 
                O      O     => true
             |  O     (S _)  => false
             | (S _)   O     => false
             | (S n1) (S m1) => (beq_nat n1 m1)
          end.

Lemma beq_nat_refl : (x:nat)true=(beq_nat x x).
Proof.
  Induction x; Simpl; Auto.
Qed.

Definition beq_nat_eq : (x,y:nat)true=(beq_nat x y)->x=y.
Proof.
  Double Induction 1 2; Simpl.
    Reflexivity.
    Intros; Discriminate H0.
    Intros; Discriminate H0.
    Intros; Case (H0 ? H1); Reflexivity.
Defined.

