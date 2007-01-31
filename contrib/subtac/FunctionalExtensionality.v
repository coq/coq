Axiom fun_extensionality : forall A B (f g : A -> B), 
  (forall x, f x = g x) -> f = g.

Axiom fun_extensionality_dep : forall A, forall B : (A -> Type), forall (f g : forall x : A, B x), 
  (forall x, f x = g x) -> f = g.

Hint Resolve fun_extensionality fun_extensionality_dep : subtac.

Require Import Coq.subtac.Utils.
Require Import Coq.subtac.FixSub.

Lemma fix_sub_eq_ext :
  forall (A : Set) (R : A -> A -> Prop) (Rwf : well_founded R)
    (P : A -> Set)
    (F_sub : forall x : A, (forall  {y : A | R y x}, P (`y)) -> P x),
    forall x : A,
      Fix_sub A R Rwf P F_sub x =
        F_sub x (fun {y : A | R y x}=> Fix A R Rwf P F_sub (`y)).
Proof.
  intros ; apply Fix_eq ; auto.
  intros.
  assert(f = g).
  apply (fun_extensionality_dep _ _ _ _ H).
  rewrite H0 ; auto.
Qed.
