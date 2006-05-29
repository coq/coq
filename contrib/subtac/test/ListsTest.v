Require Import Coq.subtac.Utils.
Require Import List.

Variable A : Set.

Program Definition myhd : forall { l : list A | length l <> 0 }, A :=  
  fun l =>
    match l with
    | nil => _
    | hd :: tl => hd
    end.
Proof.
  destruct l ; simpl ; intro H ; rewrite <- H in n ; intuition.
Defined.


Extraction myhd.
Extraction Inline proj1_sig.

Program Definition mytail : forall { l : list A | length l <> 0 }, list A :=
  fun l => 
    match l with
    | nil => _
    | hd :: tl => tl
    end.
Proof.
destruct l ; simpl ; intro H ; rewrite <- H in n ; intuition.
Defined.

Extraction mytail.

Variable a : A.

Program Definition test_hd : A := myhd (cons a nil).
Proof.
simpl ; auto.
Defined.

Extraction test_hd.

(*Program Definition test_tail : list A := mytail nil.*)





Program Fixpoint append (l : list A) (l' : list A) { struct l } :
 { r : list A | length r = length l + length l' } :=
 match l with
 | nil => l'
 | hd :: tl => hd :: (append tl l')
 end.
simpl.
subst ; auto.
simpl ; rewrite (subset_simpl (append tl0 l')).
simpl ; subst.
simpl ; auto.
Defined.

Extraction append.


Program Lemma append_app' : forall l : list A, l = append nil l.
Proof.
simpl ; auto.
Qed.

Program Lemma append_app : forall l : list A, l = append l nil.
Proof.
intros.
induction l ; simpl ; auto.
simpl in IHl.
rewrite <- IHl.
reflexivity.
Qed.




















