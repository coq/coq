(* Ancien bug signale par Laurent Thery sur la condition de garde *)

Require Import Bool.
Require Import ZArith.

Definition rNat := positive.

Inductive rBoolOp : Set :=
  | rAnd : rBoolOp
  | rEq : rBoolOp.

Definition rlt (a b : rNat) : Prop := Pos.compare_cont Eq a b = Lt.

Definition rltDec : forall m n : rNat, {rlt m n} + {rlt n m \/ m = n}.
Proof.
intros n m; generalize (nat_of_P_lt_Lt_compare_morphism n m);
 generalize (nat_of_P_gt_Gt_compare_morphism n m);
 generalize (Pcompare_Eq_eq n m); case (Pos.compare_cont Eq n m).
intros H' H'0 H'1; right; right; auto.
intros H' H'0 H'1; left; unfold rlt.
apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
intros H' H'0 H'1; right; left; unfold rlt.
apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
apply H'0; auto.
Defined.


Definition rmax : rNat -> rNat -> rNat.
Proof.
intros n m; case (rltDec n m); intros Rlt0.
exact m.
exact n.
Defined.

Inductive rExpr : Set :=
  | rV : rNat -> rExpr
  | rN : rExpr -> rExpr
  | rNode : rBoolOp -> rExpr -> rExpr -> rExpr.

Fixpoint maxVar (e : rExpr) : rNat :=
  match e with
  | rV n => n
  | rN p => maxVar p
  | rNode n p q => rmax (maxVar p) (maxVar q)
  end.

(* Check bug #1491 *)

Require Import Streams.

Definition decomp (s:Stream nat) : Stream nat :=
  match s with Cons _ s => s end.

CoFixpoint bx0 : Stream nat := Cons 0 bx1
with bx1 : Stream nat := Cons 1 bx0.

Lemma bx0bx : decomp bx0 = bx1.
simpl. (* used to return bx0 in V8.1 and before instead of bx1 *)
reflexivity.
Qed.

(* Check mutually inductive statements *)

Require Import ZArith_base Omega.
Open Scope Z_scope.

Inductive even: Z -> Prop :=
| even_base: even 0
| even_succ: forall n, odd (n - 1) -> even n
with odd: Z -> Prop :=
| odd_succ: forall n, even (n - 1) -> odd n.

Lemma even_pos_odd_pos: forall n, even n -> n >= 0
with odd_pos_even_pos : forall n, odd n -> n >= 1.
Proof.
 intros.
 destruct H.
   omega.
   apply odd_pos_even_pos in H.
   omega.
 intros.
 destruct H.
  apply even_pos_odd_pos in H.
  omega.
Qed.

CoInductive a : Prop := acons : b -> a
with b : Prop := bcons : a -> b.

Lemma a1 : a
with b1 : b.
Proof.
apply acons.
assumption.

apply bcons.
assumption.
Qed.
