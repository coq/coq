(* -*- coq-prog-args: ("-emacs-U" "-debug") -*- *)
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
  Obligations Tactic := idtac.
  Program Fixpoint map_rec ( l' : list U | sub_list l' l )
    { measure length l' } : { r : list V | length r = length l' } :=
    match l' with
    nil => nil
    | cons x tl => let tl' := map_rec tl in
	f x :: tl'
    end.
    
    Obligation 1.
    intros.
    unfold proj1_sig in map_rec.
    intros.
    destruct l' ; subtac_simpl.
    rewrite <- Heq_l'.
    auto.
    Qed.

    Obligation 2.
    simpl.
    intros.
    destruct l'.
    subtac_simpl.
    inversion s.
    unfold sub_list. 
    intuition.
    Qed.


    Obligation 3 of map_rec.
    simpl.
    intros.
    rewrite <- Heq_l'.
    simpl ; auto with arith.
    Qed.

    Obligation 4.
    simpl.
    intros.
    destruct l'.
    simpl in Heq_l'.
    destruct x0 ; simpl ; try discriminate.
    inversion Heq_l'.
    subst x tl.
    inversion s.
    apply H.
    auto with datatypes.
    Qed.
  
    Obligation 5.
    Proof.
      intros.
      destruct tl'.
      destruct l'.
      simpl in *.
      subst.
      simpl.
      subtac_simpl.
      simpl ; rewrite e ; auto.
    Qed.
    
    Program Definition map : list V := map_rec l.
    Obligation 1.
      split ; auto.
    Qed.
    
End Map_DependentRecursor.

Extraction map.
Extraction map_rec.

