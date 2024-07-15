Module Foo.
  Definition binary A := A -> A -> Prop.

  Definition inter A (R1 R2 : binary A): binary A :=
    fun (x y:A) => R1 x y /\ R2 x y.
End Foo.

Module Simple_sparse_proof.
  Parameter node : Type.
  Parameter graph : Type.
  Parameter has_edge : graph -> node -> node -> Prop.
  Implicit Types x y z : node.
  Implicit Types G : graph.

  Parameter mem : forall A, A -> list A -> Prop.
  Axiom mem_nil : forall x, mem node x nil = False.

  Definition notin (l: list node): node -> node -> Prop :=
    fun x y => ~ mem node x l /\ ~ mem node y l.

  Definition edge_notin G l : node -> node -> Prop :=
    Foo.inter node (has_edge G) (notin l).

  #[export] Hint Unfold Foo.inter notin edge_notin : rel_crush.

  Lemma edge_notin_nil G : forall x y, edge_notin G nil x y <-> has_edge G x y.
  Proof.
    intros. autounfold with rel_crush. rewrite !mem_nil. tauto.
  Qed.
End Simple_sparse_proof.
