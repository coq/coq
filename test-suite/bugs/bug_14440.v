Axioms
  (P : unit -> Type)
  (P_intro : forall u, P u)

  (Q : forall u, P u -> Type)
  (Q_intro : forall u, Q u (P_intro u))

  (Q' : forall u, P u -> Prop)
  (Q_intro' : forall u, Q' u (P_intro u)).

Set Universe Polymorphism.

Lemma broken (c d : unit) (E : c = d) :
  Q d (eq_rect c P (P_intro c) d E).
Proof.
  subst d. exact (Q_intro c).
Qed. (* Anomaly "in Univ.repr: Universe Test.441 undefined." *)

Lemma broken' (c d : unit) (E : c = d) :
  Q' d (eq_rect c P (P_intro c) d E).
Proof.
  subst d. exact (Q_intro' c).
Qed.
(* Q : forall u, P u -> Prop
   gives Anomaly
   "File "kernel/term_typing.ml", line 278, characters 7-13: Assertion failed." *)
