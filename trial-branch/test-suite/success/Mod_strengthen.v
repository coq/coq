Module Type Sub.
  Axiom Refl1 : forall x : nat, x = x.
  Axiom Refl2 : forall x : nat, x = x.
  Axiom Refl3 : forall x : nat, x = x.
  Inductive T : Set :=
      A : T.
End Sub.

Module Type Main.
  Declare Module M: Sub.
End Main.


Module A <: Main.
  Module M <: Sub.
    Lemma Refl1 : forall x : nat, x = x.
      intros; reflexivity.
    Qed.
    Axiom Refl2 : forall x : nat, x = x.
    Lemma Refl3 : forall x : nat, x = x.
      intros; reflexivity.
    Defined.
    Inductive T : Set :=
        A : T.
  End M.
End A.



(* first test *)

Module F (S: Sub).
  Module M := S.
End F.

Module B <: Main with Module M:=A.M := F A.M.



(* second test *)

Lemma r1 : (A.M.Refl1 = B.M.Refl1).
Proof.
  reflexivity.
Qed.

Lemma r2 : (A.M.Refl2 = B.M.Refl2).
Proof.
  reflexivity.
Qed.

Lemma r3 : (A.M.Refl3 = B.M.Refl3).
Proof.
  reflexivity.
Qed.

Lemma t : (A.M.T = B.M.T).
Proof.
  reflexivity.
Qed.

Lemma a : (A.M.A = B.M.A).
Proof.
  reflexivity.
Qed.


