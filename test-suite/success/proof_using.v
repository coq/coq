Require Import TestSuite.admit.
Section Foo.

Variable a : nat.

Lemma l1 : True.
Fail Proof using non_existing.
Proof using a.
exact I.
Qed.

Lemma l2 : True.
Proof using a.
Admitted.

Lemma l3 : True.
Proof using a.
admit.
Qed.

End Foo.

Check (l1 3).
Check (l2 3).
Check (l3 3).

Section Bar.

Variable T : Type.
Variable a b : T.
Variable H : a = b.

Lemma l4 : a = b.
Proof using H.
exact H.
Qed.

End Bar.

Check (l4 _ 1 1 _ : 1 = 1).

Section S1.

Variable v1 : nat.

Section S2.

Variable v2 : nat.

Lemma deep : v1 = v2.
Proof using v1 v2.
admit.
Qed.

Lemma deep2 : v1 = v2.
Proof using v1 v2.
Admitted.

End S2.

Check (deep 3 : v1 = 3).
Check (deep2 3 : v1 = 3).

End S1.

Check (deep 3 4 : 3 = 4).
Check (deep2 3 4 : 3 = 4).


Section P1.

Variable x : nat.
Variable y : nat.
Variable z : nat.


Collection TOTO := x y.

Collection TITI := TOTO - x.

Lemma t1 : True. Proof using TOTO. trivial. Qed.
Lemma t2 : True. Proof using TITI. trivial. Qed.

 Section P2.
 Collection TOTO := x.
 Lemma t3 : True. Proof using TOTO. trivial. Qed.
 End P2.

Lemma t4 : True. Proof using TOTO. trivial. Qed.

End P1.

Lemma t5 : True. Fail Proof using TOTO. trivial. Qed.

Check (t1 1 2 : True).
Check (t2 1 : True).
Check (t3 1 : True).
Check (t4 1 2 : True).


Section T1.

Variable x : nat.
Hypothesis px : 1 = x.
Let w := x + 1.

Set Suggest Proof Using.

Set Default Proof Using "Type".

Lemma bla : 2 = w.
Proof.
admit.
Qed.

End T1.

Check (bla 7 : 2 = 8).

Section A.
Variable a : nat.
Variable b : nat.
Variable c : nat.
Variable H1 : a = 3.
Variable H2 : a = 3 -> b = 7.
Variable H3 : c = 3.

Lemma foo : a = a.
Proof using Type*.
pose H1 as e1.
pose H2 as e2.
reflexivity.
Qed.

Lemma bar : a = 3 -> b = 7.
Proof using b*.
exact H2.
Qed.

Lemma baz : c=3.
Proof using c*.
exact H3.
Qed.

Lemma baz2 : c=3.
Proof using c* a.
exact H3.
Qed.

End A.

Check (foo 3 7 (refl_equal 3)
               (fun _ => refl_equal 7)).
Check (bar 3 7 (refl_equal 3)
               (fun _ => refl_equal 7)).
Check (baz2 99 3 (refl_equal 3)).
Check (baz 3 (refl_equal 3)).

Section Let.

Variables a b : nat.
Let pa : a = a. Proof. reflexivity. Qed.
Unset Default Proof Using.
Set Suggest Proof Using.
Lemma test_let : a = a.
Proof using a.
exact pa.
Qed.

Let ppa : pa = pa. Proof. reflexivity. Qed.

Lemma test_let2 : pa = pa.
Proof using Type.
exact ppa.
Qed.

End Let.

Check (test_let 3).

(* Disabled
Section Clear.

Variable a: nat.
Hypotheses H : a = 4.

Set Proof Using Clear Unused.

Lemma test_clear : a = a.
Proof using a.
Fail rewrite H.
trivial.
Qed.

End Clear.
*)

Module InteractiveUsing.

Section S.

Variable m : nat.
Variable e : m = m.

#[using="e"]
Definition a := 0.

#[using="e"]
Definition a' : nat.
exact 0.
Defined.

#[using="e"]
Fixpoint f (n:nat) : nat :=
 match n with 0 => 0 | S n => f n end.

#[using="e"]
Fixpoint f' (n:nat) : nat.
exact (match n with 0 => 0 | S n => f n end).
Defined.

#[using="Type"]
Fixpoint f1 (n:nat) : nat :=
  match n with 0 => 0 | S n => match f2 n with eq_refl => n end end
with f2 (n:nat) : m = m :=
  match n with 0 => eq_refl | S n => match f1 n with 0 => eq_refl | S _ => eq_refl end end.

#[using="Type"]
Fixpoint f1' (n:nat) : nat with f2' (n:nat) : m = m.
exact (match n with 0 => 0 | S n => match f2' n with eq_refl => n end end).
exact (match n with 0 => eq_refl | S n => match f1' n with 0 => eq_refl | S _ => eq_refl end end).
Defined.

CoInductive Stream : Set := Cons : Stream -> Stream.

#[using="e"]
CoFixpoint g : Stream := Cons g.

#[using="e"]
CoFixpoint g' : Stream.
exact (Cons g).
Defined.

#[using="e"]
Lemma g1 (n:nat) : nat with g2 (n:nat) : m = m.
exact (match n with 0 => 0 | S n => match g2 n with eq_refl => n end end).
exact (match n with 0 => eq_refl | S n => match g1 n with 0 => eq_refl | S _ => eq_refl end end).
Defined.

#[using="Type"]
Lemma g1' (n:nat) : nat with g2' (n:nat) : m = m.
exact (match n with 0 => 0 | S n => match g2' n with eq_refl => n end end).
exact (match n with 0 => eq_refl | S n => match g1' n with 0 => eq_refl | S _ => eq_refl end end).
Defined.

End S.

Check eq_refl : a 0 (eq_refl 0) = 0.
Check eq_refl : a' 0 (eq_refl 0) = 0.
Check eq_refl : f 10 (eq_refl 10) 2 = 0.
Check eq_refl : f' 10 (eq_refl 10) 2 = 0.
Check eq_refl : f1 10 2 = 1.
Check eq_refl : f1' 10 2 = 1.
Check g 0 eq_refl : Stream.
Check g' 0 eq_refl : Stream.
Check eq_refl : g1 10 (eq_refl 10) 2 = 1.
Check eq_refl : g1' 10 2 = 1.

End InteractiveUsing.
