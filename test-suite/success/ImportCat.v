Axioms A B C D : Type.
Axiom a : A.
Module M.
  Axiom AB : A -> B.
  Coercion AB : A >-> B.

  Module Inner.
    Axiom BC : B -> C.
    Coercion BC : B >-> C.
  End Inner.
  Export Inner.

  Module Alt.
    Axiom BD : B -> D.
    Coercion BD : B >-> D.
  End Alt.

  Notation "x <<< y" := (x + y) (at level 22).

  Reserved Notation "@@".

  Tactic Notation "@@" := idtac.
End M.

Module N.
    Notation "x <<< y" := (x - y) (at level 23).
End N.

Fail Import(coercions) M(AB).

Module Test1.
  Import(coercions) M.
  Check a : B.
  Check a : C.
  Fail Check a : D.

  (* names not imported *)
  Fail Import Alt.
  Fail Check AB.
  Check M.AB.

  Import M.Alt.
  Check a : D.

  Import N. (* notations didn't get imported *)
End Test1.

Module Test2.
  Import -(coercions) M.
  Fail Check a : B.
  Check AB.
  Fail Check AB a : C.

  Fail Import N.

  Check Inner.BC.
  Import Inner.
  Check AB a : C.
  Fail Check a : C.
End Test2.

Module TestExport.
  Import M(AB).
  Module Import(notations) X.
    Module Y.
      Definition bla := 0.
      Coercion AB : A >-> B.
    End Y.
    Export(coercions) Y.
  End X.

  Fail Check a : B.

  Import X.
  Check a : B.
  Fail Check bla.
  Check Y.bla.
End TestExport.

Module Notas.
  Import -(ltac.notations,notations) M.

  Import N.

  Check eq_refl : 1 <<< 1 = 0.

  Module X.
      Tactic Notation "@@" := fail.
      Lemma foo : False.
      Proof. Fail @@. Abort.
  End X.

  Import (ltac.notations) M.

  Lemma foo : False.
  Proof. @@. Abort.
End Notas.
