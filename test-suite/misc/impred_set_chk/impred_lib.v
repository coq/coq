(* Constants and inductives with and without actual reliance on
   impredicative Set; the checker validates the stored usage bits. *)
Definition impred_def : Set := forall X : Set, X -> X.
Definition impred_unused : nat := 0.
Definition fires_but_unused : Type := forall X : Set, X -> X.
Inductive impred_ind : Set := mk_impred : (forall X : Set, X) -> impred_ind.
Inductive param_ind (A : Prop) : Set := mk_param : A -> param_ind A.
Lemma opaque_used : True.
Proof. exact (let x : Set := forall X : Set, X -> X in I). Qed.
Lemma opaque_unused : True.
Proof. exact I. Qed.
