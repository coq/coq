Module Type Sub.
  Axiom Refl1 : (x:nat)(x=x).
  Axiom Refl2 : (x:nat)(x=x).
  Axiom Refl3 : (x:nat)(x=x).
  Inductive T : Set := A : T.
End Sub.

Module Type Main.
  Declare Module M:Sub.
End Main.


Module A <: Main.
  Module M <: Sub.
    Lemma Refl1 : (x:nat) x=x.
      Intros;Reflexivity.
    Qed.
    Axiom Refl2 : (x:nat) x=x.
    Lemma Refl3 : (x:nat) x=x.
      Intros;Reflexivity.
    Defined.
    Inductive T : Set := A : T.
  End M.
End A.



(* first test *)

Module F[S:Sub].
  Module M:=S.
End F.

Module B <: Main with Module M:=A.M := F A.M.



(* second test *)

Lemma r1 : (A.M.Refl1 == B.M.Refl1).
Proof.
  Reflexivity.
Qed.

Lemma r2 : (A.M.Refl2 == B.M.Refl2).
Proof.
  Reflexivity.
Qed.

Lemma r3 : (A.M.Refl3 == B.M.Refl3).
Proof.
  Reflexivity.
Qed.

Lemma t : (A.M.T == B.M.T).
Proof.
  Reflexivity.
Qed.

Lemma a : (A.M.A == B.M.A).
Proof.
  Reflexivity.
Qed.

