Definition ptr64 := false.

Inductive val: Set := Vundef: val.

Inductive lessdef: val -> val -> Prop := lessdef_undef: forall v, lessdef Vundef v.

Global Hint Resolve lessdef_undef : foo.

Axiom memval : Set.
Axiom load_result : memval -> val.

Lemma foo : forall (v : val)
  (vl' : memval), lessdef (if ptr64 then load_result vl' else Vundef) v.
Proof.
intros vl'.
auto with foo.
Qed.
