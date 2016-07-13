Set Primitive Projections.

Record foo : Type := bar { x : unit }.

Goal forall t u, bar t = bar u -> t = u.
Proof.
  intros.
  injection H.
  trivial.
Qed.
(* Was: Error: Pattern-matching expression on an object of inductive type foo has invalid information. *)

(** Dependent pattern-matching is ok on this one as it has eta *)
Definition baz (x : foo) :=
  match x as x' return x' = x' with
  | bar u => eq_refl
  end.

Inductive foo' : Type := bar' {x' : unit; y: foo'}.
(** Dependent pattern-matching is not ok on this one *)
Fail Definition baz' (x : foo') :=
  match x as x' return x' = x' with
  | bar' u y => eq_refl
  end.
