Module Type SIG.
  Inductive w : Set :=
      A : w.
  Parameter f : w -> w.
End SIG.

Module M : SIG.
  Inductive w : Set :=
      A : w.
  Definition f x := match x with
                    | A => A
                    end.
End M.

Module N := M.

Check (N.f M.A).

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
  intro x. unfold B.f, A.f.
  destruct x; reflexivity.
  Qed.

  (* Check equivalence is considered in pattern-matching *)
  Definition f (x : A.t) := match x with B.A.a => true | B.A.b => false end.

  End C.

