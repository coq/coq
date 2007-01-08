Require Import Wf.
Require Import Coq.subtac.Utils.

Section Well_founded.
  Variable A : Set.
  Variable R : A -> A -> Prop.
  Hypothesis Rwf : well_founded R.
  
  Section Acc.
    
    Variable P : A -> Set.
    
    Variable F_sub : forall x:A, (forall y: { y : A | R y x }, P (proj1_sig y)) -> P x.
    
    Fixpoint Fix_F_sub (x : A) (r : Acc R x) {struct r} : P x :=
      F_sub x (fun y: { y : A | R y x}  => Fix_F_sub (proj1_sig y) 
        (Acc_inv r (proj1_sig y) (proj2_sig y))).
    
    Definition Fix_sub (x : A) := Fix_F_sub x (Rwf x).
  End Acc.
  
  Section FixPoint.
    Variable P : A -> Set.
    
    Variable F_sub : forall x:A, (forall y: { y : A | R y x }, P (proj1_sig y)) -> P x.
    
    Notation Fix_F := (Fix_F_sub P F_sub) (only parsing). (* alias *)
    
    Definition Fix (x:A) := Fix_F_sub P F_sub x (Rwf x).
    
    Hypothesis
      F_ext :
      forall (x:A) (f g:forall y:{y:A | R y x}, P (`y)),
        (forall y:{ y:A | R y x}, f y = g y) -> F_sub x f = F_sub x g.

    Lemma Fix_F_eq :
      forall (x:A) (r:Acc R x),
        F_sub x (fun (y:{y:A|R y x}) => Fix_F (`y) (Acc_inv r (proj1_sig y) (proj2_sig y))) = Fix_F x r.
    Proof. 
      destruct r using Acc_inv_dep; auto.
    Qed.
    
    Lemma Fix_F_inv : forall (x:A) (r s:Acc R x), Fix_F x r = Fix_F x s.
    Proof.
      intro x; induction (Rwf x); intros.
      rewrite <- (Fix_F_eq x r); rewrite <- (Fix_F_eq x s); intros.
      apply F_ext; auto.
      intros.
      rewrite (proof_irrelevance (Acc R x) r s) ; auto.
    Qed.

    Lemma Fix_eq : forall x:A, Fix x = F_sub x (fun (y:{y:A|R y x}) => Fix (proj1_sig y)).
    Proof.
      intro x; unfold Fix in |- *.
      rewrite <- (Fix_F_eq ).
      apply F_ext; intros.
      apply Fix_F_inv.
    Qed.

    Lemma fix_sub_eq :
        forall x : A,
          Fix_sub P F_sub x =
          let f_sub := F_sub in
            f_sub x (fun  {y : A | R y x}=> Fix (`y)).
      exact Fix_eq.
    Qed.

 End FixPoint.

End Well_founded.

Extraction Inline Fix_F_sub Fix_sub.

Require Import Wf_nat.
Require Import Lt.

Section Well_founded_measure.
Variable A : Set.
Variable f : A -> nat.
Definition R := fun x y => f x < f y.

Section FixPoint.

Variable P : A -> Set.

Variable F_sub : forall x:A, (forall y: { y : A | f y < f x }, P (proj1_sig y)) -> P x.
 
Fixpoint Fix_measure_F_sub (x : A) (r : Acc lt (f x)) {struct r} : P x :=
   F_sub x (fun y: { y : A | f y < f x}  => Fix_measure_F_sub (proj1_sig y) 
   (Acc_inv r (f (proj1_sig y)) (proj2_sig y))).

Definition Fix_measure_sub (x : A) := Fix_measure_F_sub x (lt_wf (f x)).

End FixPoint.

End Well_founded_measure.

Extraction Inline Fix_measure_F_sub Fix_measure_sub.
