Module File1.
  Module Export DirA.
    Module A.
      Inductive paths {A : Type} (a : A) : A -> Type :=
        idpath : paths a a.

      Arguments idpath {A a} , [A] a.

      Notation "x = y :> A" := (@paths A x y) : type_scope.
      Notation "x = y" := (x = y :>_) : type_scope.
    End A.
  End DirA.
End File1.

Module File2.
  Module Export DirA.
    Module B.
      Import File1.
      Export A.
      Lemma foo : forall x y : Type, x = y -> y = x.
      Proof.
        intros x y H.
        rewrite <- H.
        constructor.
      Qed.
    End B.
  End DirA.
End File2.

Module File3.
  Module Export DirA.
    Module C.
      Import File1.
      Export A.
      Lemma bar : forall x y : Type, x = y -> y = x.
      Proof.
        intros x y H.
        rewrite <- H.
        constructor.
      Defined.
      Definition bar'
        := Eval cbv beta iota zeta delta [bar internal_paths_rew] in bar.
    End C.
  End DirA.
End File3.
