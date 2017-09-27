Set Suggest Proof Using.

Section Sec.
  Variables A B : Type.

  (* Some normal lemma. *)
  Lemma nat : Set.
  Proof.
    exact nat.
  Qed.

  (* Make sure All is suggested even though we add an unused variable
  to the context. *)
  Let foo : Type.
  Proof.
    exact (A -> B).
  Qed.

  (* Having a [Proof using] disables the suggestion message. *)
  Definition bar : Type.
  Proof using A.
    exact A.
  Qed.

  (* Transparent definitions don't get a suggestion message. *)
  Definition baz : Type.
  Proof.
    exact A.
  Defined.

End Sec.
