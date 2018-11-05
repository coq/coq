
(* Check use of equivalence on inductive types (bug #1242) *)

Module Type ASIG.
  Inductive t : Set := a | b : t.
  Definition f := fun x => match x with a => true | b => false end.
End ASIG.

Module Type BSIG.
  Declare Module A : ASIG.
  Definition f := fun x => match x with A.a => true | A.b => false end.
End BSIG.

Module C (A : ASIG) (B : BSIG with Module A:=A).

  (* Check equivalence is considered in "case_info" *)
  Lemma test : forall x, A.f x = B.f x.
  Proof.
    intro x. unfold B.f, A.f.
    destruct x; reflexivity.
  Qed.

End C.
