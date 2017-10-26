Require Import TestSuite.admit.

Require Import Relations Program Setoid Morphisms.

Section S1.
  Variable R: nat -> relation bool.
  Instance HR1: forall n, Transitive (R n). Admitted.
  Instance HR2: forall n, Symmetric (R n).  Admitted.
  Hypothesis H: forall n a, R n (andb a a) a.
  Goal forall n a b, R n b a.
   intros. 
   (* rewrite <- H. *) (* Anomaly: Evar ?.. was not declared. Please report. *)
   (* idem with setoid_rewrite *)
(*    assert (HR2' := HR2 n). *)
   rewrite <- H.                (* ok *)
   admit.
  Qed.
End S1.

Section S2.
  Variable R: nat -> relation bool.
  Instance HR: forall n, Equivalence (R n). Admitted.
  Hypothesis H: forall n a, R n (andb a a) a.
  Goal forall n a b, R n a b.
   intros. rewrite <- H. admit.
  Qed.
End S2.

(* the parametrised relation is required to get the problem *)
Section S3.
  Variable R: relation bool.
  Instance HR1': Transitive R. Admitted.
  Instance HR2': Symmetric R.  Admitted.
  Hypothesis H: forall a, R (andb a a) a.
  Goal forall a b, R b a.
   intros. 
   rewrite <- H.                (* ok *)
   admit.
  Qed.
End S3.
