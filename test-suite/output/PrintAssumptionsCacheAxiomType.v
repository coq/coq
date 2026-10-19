(* Print Assumptions reuses traversals across queries in one environment.
   An axiom's type is traversed too: whatever it reaches must still be
   printed when the axiom is reached through an object an earlier query
   already traversed. *)

Module TwoRoots.
  Lemma secret : nat. Proof. exact 0. Admitted.
  Axiom gate : (fun _ : nat => nat) secret.
  Definition one : nat := gate.
  Definition two : nat := S gate.
  Print Assumptions one.
  Print Assumptions two.
  Print Assumptions one.
End TwoRoots.

Module SameRoot.
  Axiom hidden : nat.
  Axiom reached_via_type : hidden = hidden -> nat.
  Definition uses : nat := reached_via_type eq_refl.
  Print Assumptions uses.
  Print Assumptions uses.
End SameRoot.

Module Beta.
  Axiom hidden : nat.
  Axiom A : (fun _ : nat => nat) hidden.
  Definition uses : nat := A.
  Lemma other : nat. Proof. exact A. Admitted.
  Print Assumptions uses.
  Print Assumptions other.
  Print Assumptions uses.
End Beta.

Module Chain.
  (* The type walk of [top_ax] reaches [mid], whose own type walk reaches
     [low]: replay must follow both levels. *)
  Axiom low : Type.
  Axiom mid : low -> Type.
  Axiom top_ax : forall l : low, mid l.
  Definition user : forall l : low, mid l := top_ax.
  Definition user2 : forall l : low, mid l := user.
  Print Assumptions user.
  Print Assumptions user2.
  Print Assumptions user.
End Chain.

Module Sibling.
  (* [B]'s type walk finds [C] already visited through [A], earlier in the
     same query; a later query on [B] alone must still reach [C]. *)
  Axiom C : Type.
  Definition A : Type := C.
  Axiom B : C.
  Definition R : Type * C := (A, B).
  Print Assumptions R.
  Print Assumptions B.
End Sibling.
