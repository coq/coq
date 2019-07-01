
Set Universe Polymorphism.

Cumulative Inductive EQ {A} (x : A) : A -> Type
  := EQ_refl : EQ x x.

Register EQ as core.eq.type.

Lemma renamed_EQ_rect {A} (x:A) (P : A -> Type)
  (c : P x) (y : A) (e : EQ x y) : P y.
Proof. destruct e. assumption. Qed.

Register renamed_EQ_rect as core.eq.rect.
Register renamed_EQ_rect as core.eq.ind.

Lemma renamed_EQ_rect_r {A} (x:A) (P : A -> Type)
  (c : P x) (y : A) (e : EQ y x) : P y.
Proof. destruct e. assumption. Qed.

Register renamed_EQ_rect_r as core.eq.rect_r.
Register renamed_EQ_rect_r as core.eq.ind_r.

Lemma EQ_sym1 {A} {x y : A} (e : EQ x y) : EQ y x.
Proof. rewrite e. reflexivity. Qed.

Lemma EQ_sym2 {A} {x y : A} (e : EQ x y) : EQ y x.
Proof. rewrite <- e. reflexivity. Qed.

Require Import ssreflect.

Lemma ssr_EQ_sym1 {A} {x y : A} (e : EQ x y) : EQ y x.
Proof. rewrite e. reflexivity. Qed.

Lemma ssr_EQ_sym2 {A} {x y : A} (e : EQ x y) : EQ y x.
Proof. rewrite -e. reflexivity. Qed.
