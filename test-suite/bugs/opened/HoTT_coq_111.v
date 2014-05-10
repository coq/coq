Module X.
  Set Universe Polymorphism.
  Inductive paths A (x : A) : forall _ : A, Type := idpath : paths A x x.
  Notation "x = y" := (@paths _ x y) (at level 70, no associativity) : type_scope.

  Axioms A B : Type.
  Axiom P : A = B.
  Definition foo : A = B.
    Fail abstract (rewrite <- P; reflexivity).
  (* Error: internal_paths_rew already exists. *)
  Admitted.
  Fail Defined. (* Anomaly: Uncaught exception Not_found(_). Please report. *)
End X.

Module Y.
  Set Universe Polymorphism.
  Inductive paths A (x : A) : forall _ : A, Type := idpath : paths A x x.
  Notation "x = y" := (@paths _ x y) (at level 70, no associativity) : type_scope.

  Axioms A B : Type.
  Axiom P : A = B.
  Definition foo : (A = B) * (A = B).
    Fail split; abstract (rewrite <- P; reflexivity).
  (* Error: internal_paths_rew already exists. *)
  Fail Defined. (* Anomaly: Uncaught exception Not_found(_). Please report. *)
Fail End Y.
