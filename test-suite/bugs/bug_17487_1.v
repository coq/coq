Section Definitions.

Variable A : Type.

Fixpoint vector (n:nat) {struct n} : Type :=
match n with
| 0  => A
| S n => (A * (vector n))%type
end.

End Definitions.

Module Test.

Parameter A : Type.

Definition vectorA : nat -> Type.
Proof.
apply (vector A).
Defined.

(** Check that head normalization of vectorA to an inductive with refolding
    correctly keeps universe constraints. See also #5645. *)
Goal forall dim (v : vectorA (S dim)), True.
Proof.
intros dim.
intros [a v].
constructor.
Qed. (* The 2nd term has type "Type@{vector.u0}" which should be coercible to "Type@{prod.u1}". *)


End Test.
