(* -*- coq-prog-args: ("-emacs-U" "-debug") -*- *)
Require Import List.
Require Import Coq.Program.Program.

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

  Obligations Tactic := unfold sub_list in * ; 
    program_simpl ; intuition.

  Program Fixpoint map_rec ( l' : list U | sub_list l' l )
    { measure length l' } : { r : list V | length r = length l' } :=
    match l' with
      | nil => nil
      | cons x tl => let tl' := map_rec tl in
	f x :: tl'
    end.
    
  Next Obligation.
    destruct_call map_rec.
    simpl in *.
    subst l'.
    simpl ; auto with arith.
  Qed.
      
  Program Definition map : list V := map_rec l.
    
End Map_DependentRecursor.

Extraction map.
Extraction map_rec.

