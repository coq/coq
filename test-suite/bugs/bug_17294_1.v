
Module Import Datatypes.

Set Implicit Arguments.
Set Primitive Projections.

Record prod (A : Type) := pair { fst : A }.

End Datatypes.

Axiom Or : Type -> Type.
Axiom to : forall T, T ->  (Or T).

Section ORecursion.
  Context {P Q : Type} .
  Definition O_rec (f : P -> Q) : (Or P) -> Q.
  Admitted.
  Definition O_rec_beta (f : P -> Q) (x : P) : O_rec f (to P x) = f x.
  Admitted.

End ORecursion.

Parameter (A : Type).

Definition O_prod_unit  : prod A -> prod (Or A).
  exact (fun (z : prod A) => pair (to A (fst z))).
Defined.

Lemma foo  (x : A)
  : O_rec O_prod_unit (to (prod A) (pair x)) = pair (to A x).
Proof.
  apply O_rec_beta.
Qed.
