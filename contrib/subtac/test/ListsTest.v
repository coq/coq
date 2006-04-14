Require Import Coq.subtac.Utils.
Require Import List.
Require Import Arith.
Variable A : Set.

Notation "` t" := (proj1_sig t) (at level 100) : core_scope.
Extraction Inline proj1_sig.
Notation "'forall' { x : A | P } , Q" :=
  (forall x:{x:A|P}, Q)
  (at level 200, x ident, right associativity).
Require Import Omega.
Program Definition myhd : 
  forall { l : list A | length l <> 0 }, A :=
  
  fun l =>
    match l with
    | nil => _
    | hd :: tl => hd
    end.

Proof.
  destruct l ; simpl ; intro H ; rewrite <- H in n ; intuition.
Defined.

Extraction myhd.

Program Definition mytail : 
  forall { l : list A | length l <> 0 }, list A :=

  fun l => 
    match `l with
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

Program Definition test_tail : list A := mytail nil.

Program Fixpoint append (l : list A) (l' : list A) { struct l } :
 { r : list A | length r = length l + length l' } :=
 match l with
 nil => l'
 | hd :: tl => hd :: (append tl l')
 end.
rewrite Heql ; auto.
simpl.
rewrite (subset_simpl (append tl0 l')).
unfold tl0 ; unfold hd0.
rewrite Heql.
simpl ; auto.
Defined.

Extraction append.

Lemma append_app' : forall l : list A, (`append nil l) = l.
Proof.
simpl ; auto.
Qed.

Lemma append_app : forall l : list A, (`append l nil) = l.
Proof.
intros.
induction l ; simpl ; auto.
simpl in IHl.
rewrite IHl.
reflexivity.
Qed.




















