Universe u v w x.
Inductive invertible {X:Type@{u}} {Y:Type} (f:X->Y) : Prop := .
Inductive FiniteT : Type -> Prop :=
  | add_finite: forall T:Type@{v}, FiniteT T -> FiniteT (option T)
  | bij_finite: forall (X:Type@{w}) (Y:Type@{x}) (f:X->Y), FiniteT X ->
    invertible f -> FiniteT Y.

Axiom a : False.

(* This bug can be triggered by restrict_context if it does not correctly compute the closure
  of constraints while removing some universes. In particular it depends on the union-find
  algorithm's choice of canonical representative in the proof below, when we are restricting
  by removing a universe that can be chosen as representative, while keeping the global [w]
  which is equal to it. *)
(* Constraint v <= u. *)
(* Constraint v <= w. *)
(* Set Debug "univMinim". *)
(* Set Debug "ustate". *)
(* Set Debug "minimization". *)
Lemma finite_subtype@{ux ?}: forall (X:Type@{ux}) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  FiniteT {x:X | P x}.
Proof.
intros.
induction H.

destruct (H0 None).
elim a.

pose (g := fun (x:{x:T | P (Some x)}) =>
  match x return {x:option T | P x} with
    | exist _ x0 i => exist (fun x:option T => P x) (Some x0) i
  end).
apply bij_finite with _ g.
apply IHFiniteT.
intro; apply H0.
elim a.

pose (g := fun (x:{x:X | P (f x)}) =>
  match x with
  | exist _ x0 i => exist (fun x:Y => P x) (f x0) i
  end).
apply bij_finite with _ g.
apply IHFiniteT.
intro; apply H0.
elim a.
Show Universes. (* Universe .15 here is = w but restricted away *)
Qed.
