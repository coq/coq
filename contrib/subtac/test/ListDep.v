Require Import List.
Require Import Coq.subtac.Utils.

Set Implicit Arguments.

Definition sub_list (A : Set) (l' l : list A) := (forall v, In v l' -> In v l) /\ length l' <= length l.

Lemma sub_list_tl : forall A : Set, forall x (l l' : list A), sub_list (x :: l) l' -> sub_list l l'.
Proof.
  intros.
  inversion H.
  split.
  intros.
  apply H0.
  auto with datatypes.
  auto with arith.
Qed.

Section Map_DependentRecursor.
  Variable U V : Set.
  Variable l : list U.
  Variable f : { x : U | In x l } -> V.

  Program Fixpoint map_rec ( l' : list U | sub_list l' l )
    { measure l' length } : { r : list V | length r = length l' } :=
    match l' with
    nil => nil
    | cons x tl => let tl' := map_rec tl in
	f x :: tl'
    end.
    
    Obligation 1.
    intros.
    destruct tl' ; simpl ; simpl in e.
    subst x0 tl0.
    rewrite <- Heql'.
    rewrite e.
    auto.
    Qed.

    Obligation 2.
    simpl.
    intros.
    destruct l'.
    simpl in Heql'.
    destruct x0 ; simpl ; try discriminate.
    inversion Heql'.
    inversion s.
    apply H.
    auto with datatypes.
    Qed.


    Obligation 3 of map_rec.
    simpl.
    intros.
    rewrite <- Heql'.
    simpl ; auto with arith.
    Qed.

    Obligation 4.
    simpl.
    intros.
    destruct l'.
    simpl in Heql'.
    destruct x0 ; simpl ; try discriminate.
    inversion Heql'.
    subst x tl.
    apply sub_list_tl with u ; auto.
    Qed.
  
    Obligation 5.
    intros.
    rewrite <- Heql' ; auto.
    Qed.
    
    Program Definition map : list V := map_rec l.
    Obligation 1.
      split ; auto.
    Qed.
    
End Map_DependentRecursor.

Extraction map.
Extraction map_rec.

