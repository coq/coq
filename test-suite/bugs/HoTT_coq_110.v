Module X.
  Inductive paths A (x : A) : A -> Type := idpath : paths A x x.
  Notation "x = y" := (@paths _ x y) : type_scope.

  Axioms A B : Type.
  Axiom P : A = B.
  Definition foo : A = B.
    abstract (rewrite <- P; reflexivity).
  (* Error: internal_paths_rew already exists. *)
  Defined. (* Anomaly: Uncaught exception Not_found(_). Please report. *)
End X.

Module Y.
  Inductive paths A (x : A) : A -> Type := idpath : paths A x x.
  Notation "x = y" := (@paths _ x y) : type_scope.

  Axioms A B : Type.
  Axiom P : A = B.
  Definition foo : (A = B) * (A = B).
    split; abstract (rewrite <- P; reflexivity).
  (* Error: internal_paths_rew already exists. *)
  Defined. (* Anomaly: Uncaught exception Not_found(_). Please report. *)
End Y.
