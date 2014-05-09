Require Export Coq.Lists.List.

Polymorphic Fixpoint LIn (A : Type) (a:A) (l:list A) : Type :=
  match l with
    | nil => False
    | b :: m => (b = a) + LIn A a m
  end.

Polymorphic Inductive NTerm : Type :=
| cterm : NTerm
| oterm : list NTerm -> NTerm.

Polymorphic Fixpoint dummy {A B} (x : list (A * B)) : list (A * B) :=
  match x with
    | nil => nil
    | (_, _) :: _ => nil
  end.

Lemma foo :
  forall v t sub vars,
    LIn (nat * NTerm) (v, t) (dummy sub)
    ->
    (
      LIn (nat * NTerm) (v, t) sub
      *
      notT (LIn nat v vars)
    ).
Proof.
  induction sub; simpl; intros.
  destruct H.
  Set Printing Universes.
  try (apply IHsub in X). (* Toplevel input, characters 5-21:
Error: Universe inconsistency (cannot enforce Top.47 = Set). *)
