Class C (x y : nat).

Global Hint Extern 0 (C _ _) => idtac "extern called"; fail : typeclass_instances.

Global Hint Mode C + + : typeclass_instances.

Goal exists x y, C x y.
Proof.
  eexists; eexists.
  Fail typeclasses eauto.
Abort.

Global Hint Mode C = - : typeclass_instances.
Global Hint Mode C - = : typeclass_instances.

Goal exists x y, C x y.
Proof.
  eexists; eexists.
  (* Each mode for [C] generates an application attempt. *)
  Fail typeclasses eauto.
Abort.

Class D (n : nat).

Axiom d_0 : D 0.
Global Hint Extern 0 (D _) =>
  idtac "guarded extern called"; exact d_0 : typeclass_instances.
Global Hint Mode D = : typeclass_instances.

Goal exists n, D n.
Proof.
  eexists.
  Fail typeclasses eauto.
Abort.
