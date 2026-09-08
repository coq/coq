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

Class E (x y : nat).

Global Hint Extern 0 (E _ _) =>
  idtac "deduplicated extern called"; fail : typeclass_instances.

Global Hint Mode E = - : typeclass_instances.
Global Hint Mode E = + : typeclass_instances.

Goal exists x, E x 0.
Proof.
  eexists.
  (* Both modes match, but impose the same frozen-evar restriction, so the
     extern hint is attempted only once. *)
  Fail typeclasses eauto.
Abort.

Definition F (x y : nat) : Prop := True.

Create HintDb hint_mode_unfold_output.
Global Hint Unfold F : hint_mode_unfold_output.
Global Hint Extern 0 True =>
  idtac "post-unfold extern called"; fail : hint_mode_unfold_output.
Global Hint Mode F = - : hint_mode_unfold_output.
Global Hint Mode F - = : hint_mode_unfold_output.

Goal exists x y, F x y.
Proof.
  eexists; eexists.
  (* Both modes produce the same unfold tactic, which must be tried only once. *)
  Fail typeclasses eauto with hint_mode_unfold_output nocore.
Abort.
