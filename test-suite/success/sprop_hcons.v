(* -*- coq-prog-args: ("-allow-sprop"); -*- *)

(* A bug due to bad hashconsing of case info *)

Inductive sBox (A : SProp) : Type :=
  sbox : A -> sBox A.

Definition ubox {A : SProp} (bA : sBox A) : A :=
  match bA with
    sbox _ X => X
  end.

Inductive sle : nat -> nat -> SProp :=
  sle_0 : forall n, sle 0 n
| sle_S : forall n m : nat, sle n m -> sle (S n) (S m).

Definition sle_Sn (n : nat) : sle n (S n).
Proof.
  induction n; constructor; auto.
Defined.

Definition sle_trans {n m p} (H : sle n m) (H': sle m  p) : sle n p.
Proof.
  revert H'. revert p. induction H.
  - intros p H'. apply sle_0.
  - intros p H'. inversion H'. apply ubox. subst. apply sbox. apply sle_S. apply IHsle;auto.
Defined.

Lemma sle_Sn_m {n m} : sle n m -> sle n (S m).
Proof.
  intros H. destruct n.
  - constructor.
  - constructor;auto. assert (H1 : sle n (S n)) by apply sle_Sn.
    exact (sle_trans H1 H ).
Defined.

Definition sle_Sn_Sm {n m} : sle (S n) (S m) -> sle n m.
Proof.
  intros H.
  inversion H. apply ubox. subst. apply sbox. exact H2.
Qed.


Notation "g ∘ f" := (sle_trans g f) (at level 40).

Lemma bazz q0 m (f : sle (S q0) (S m)) :
  sbox _ (sle_Sn q0 ∘ f) = sbox _ (sle_Sn_m (sle_Sn_Sm f)).
Proof.
  reflexivity. (* used to fail *)
  (* NB: exact eq_refl succeeded even with the bug so no guarantee
  that this test will continue to test the right thing. *)
Qed.
