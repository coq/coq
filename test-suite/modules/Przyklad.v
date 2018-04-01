Definition ifte (T : Set) (A B : Prop) (s : {A} + {B})
  (th el : T) := if s then th else el.

Arguments ifte : default implicits.

Lemma Reflexivity_provable :
 forall (A : Set) (a : A) (s : {a = a} + {a <> a}),
 exists x : _, s = left _ x.
intros.
elim s.
intro x.
split with x; reflexivity.

intro.
 absurd (a = a); auto.

Qed.

Lemma Disequality_provable :
 forall (A : Set) (a b : A),
 a <> b -> forall s : {a = b} + {a <> b}, exists x : _, s = right _ x.
intros.
elim s.
intro.
 absurd (a = a); auto.

intro.
split with b0; reflexivity.

Qed.

Module Type ELEM.
  Parameter T : Set.
  Parameter eq_dec : forall a a' : T, {a = a'} + {a <> a'}.
End ELEM.

Module Type SET (Elt: ELEM).
  Parameter T : Set.
  Parameter empty : T.
  Parameter add : Elt.T -> T -> T.
  Parameter find : Elt.T -> T -> bool.

  (* Axioms *)

  Axiom find_empty_false : forall e : Elt.T, find e empty = false.

  Axiom find_add_true : forall (s : T) (e : Elt.T), find e (add e s) = true.

  Axiom
    find_add_false :
      forall (s : T) (e e' : Elt.T), e <> e' -> find e (add e' s) = find e s.

End SET.

Module FuncDict (E: ELEM).
  Definition T := E.T -> bool.
  Definition empty (e' : E.T) := false.
  Definition find (e' : E.T) (s : T) := s e'.
  Definition add (e : E.T) (s : T) (e' : E.T) :=
    ifte (E.eq_dec e e') true (find e' s).

  Lemma find_empty_false : forall e : E.T, find e empty = false.
    auto.
  Qed.

  Lemma find_add_true : forall (s : T) (e : E.T), find e (add e s) = true.

    intros.
    unfold find, add.
    elim (Reflexivity_provable _ _ (E.eq_dec e e)).
    intros.
     rewrite H.
    auto.

  Qed.

  Lemma find_add_false :
   forall (s : T) (e e' : E.T), e <> e' -> find e (add e' s) = find e s.
    intros.
    unfold add, find.
    cut (exists x : _, E.eq_dec e' e = right _ x).
    intros.
    elim H0.
    intros.
     rewrite H1.
    unfold ifte.
    reflexivity.

    apply Disequality_provable.
    auto.

  Qed.

End FuncDict.

Module F : SET := FuncDict.


Module Nat.
  Definition T := nat.
  Lemma eq_dec : forall a a' : T, {a = a'} + {a <> a'}.
     decide equality.
  Qed.
End Nat.


Module SetNat := F Nat.


Lemma no_zero_in_empty : SetNat.find 0 SetNat.empty = false.
apply SetNat.find_empty_false.
Qed.

(***************************************************************************)
Module Lemmas (G: SET) (E: ELEM).

  Module ESet := G E.

  Lemma commute :
   forall (S : ESet.T) (a1 a2 : E.T),
   let S1 := ESet.add a1 (ESet.add a2 S) in
   let S2 := ESet.add a2 (ESet.add a1 S) in
   forall a : E.T, ESet.find a S1 = ESet.find a S2.

    intros.
    unfold S1, S2.
    elim (E.eq_dec a a1); elim (E.eq_dec a a2); intros H1 H2;
     try  rewrite <- H1; try  rewrite <- H2;
     repeat
      (try ( rewrite ESet.find_add_true; auto);
        try ( rewrite ESet.find_add_false; auto); auto).
  Qed.
End Lemmas.


Inductive list (A : Set) : Set :=
  | nil : list A
  | cons : A -> list A -> list A.

Module ListDict (E: ELEM).
  Definition T := list E.T.
  Definition elt := E.T.

  Definition empty := nil elt.
  Definition add (e : elt) (s : T) := cons elt e s.
  Fixpoint find (e : elt) (s : T) {struct s} : bool :=
    match s with
    | nil _ => false
    | cons _ e' s' => ifte (E.eq_dec e e') true (find e s')
    end.

  Definition find_empty_false (e : elt) := refl_equal false.

  Lemma find_add_true : forall (s : T) (e : E.T), find e (add e s) = true.
    intros.
    simpl.
    elim (Reflexivity_provable _ _ (E.eq_dec e e)).
    intros.
     rewrite H.
    auto.

  Qed.


  Lemma find_add_false :
   forall (s : T) (e e' : E.T), e <> e' -> find e (add e' s) = find e s.
    intros.
    simpl.
    elim (Disequality_provable _ _ _ H (E.eq_dec e e')).
    intros.
     rewrite H0.
    simpl.
    reflexivity.
  Qed.


End ListDict.


Module L : SET := ListDict.







