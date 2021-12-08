(*I get an Anomaly in the following code.

```*)
Require Vector.

Module M.
  Lemma Vector_map_map :
    forall A B C (f : A -> B) (g : B -> C) n (v : Vector.t A n),
      Vector.map g (Vector.map f v) = Vector.map (fun a => g (f a)) v.
  Proof.
    induction v; simpl; auto using f_equal.
  Qed.

  Lemma Vector_map_map_transparent :
    forall A B C (f : A -> B) (g : B -> C) n (v : Vector.t A n),
      Vector.map g (Vector.map f v) = Vector.map (fun a => g (f a)) v.
  Proof.
    induction v; simpl; auto using f_equal.
  Defined.
  (* Anomaly: constant not found in kind_of_head: Coq.Vectors.Vector.t_ind. Please report. *)

  (* strangely, explicitly passing the principle to induction works *)
  Lemma Vector_map_map_transparent' :
    forall A B C (f : A -> B) (g : B -> C) n (v : Vector.t A n),
      Vector.map g (Vector.map f v) = Vector.map (fun a => g (f a)) v.
  Proof.
    induction v using Vector.t_ind; simpl; auto using f_equal.
  Defined.
End M.
(*```

Changing any of the following things eliminates the Anomaly
   * moving the lemma out of the module M to the top level
   * proving the lemma as a Fixpoint instead of using induction
   * proving the analogous lemma on lists instead of vectors*)
