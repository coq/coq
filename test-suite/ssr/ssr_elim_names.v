From Coq Require Import ssreflect.
Open Scope ssrelim_scope.

Inductive t := K (a : t).

Axiom q : t -> Prop.

Inductive p : t -> Prop :=
| Rule_1 y : p y
| Rule_for_K x t :
                  q x   # q_x
                  p t   # p_t__IHt
                (* ----*)
                  p (K t).

Lemma test x (H : p x) : q x.
Proof.
elim: H => [^~ 1].
  Check y1 : t.
  admit.
Check x1 : t.
Check t1 : t.
Check q_x1 : q x1.
Check p_t1 : p t1.
Check IHt1 : q t1.
Admitted.
