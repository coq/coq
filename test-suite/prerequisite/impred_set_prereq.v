(* -*- coq-prog-args: ("-impredicative-set"); -*- *)
Definition impred_def : Set := forall X : Set, X -> X.
Inductive impred_ind : Set := mk_impred : (forall X : Set, X) -> impred_ind.
Inductive normal_ind : Set := mk_normal : True -> normal_ind.
Definition impred_unused : nat := 0.
Definition IdSet (A : Set) : Set := A.
Definition impred_def_nested := IdSet (forall X : Set, X -> X).
Inductive impred_ind_nested : Set := mk_nested : IdSet (forall X : Set, X -> X) -> impred_ind_nested.
(* The impredicative product rule fires here (the body is assigned sort
   Set where predicative inference gives Type), but cumulativity absorbs
   the difference: no actual reliance. *)
Definition impred_fires_but_unused : Type := forall X : Set, X -> X.
(* Reliance inside an opaque proof body. *)
Lemma impred_opaque_used : True.
Proof. exact (let x : Set := forall X : Set, X -> X in I). Qed.
Lemma impred_opaque_unused : True.
Proof. exact I. Qed.
(* Parameterized inductives: binding of the block's inductives vs
   parameters in the predicative recheck. *)
Inductive param_ind (A : Prop) : Set := mk_param : A -> param_ind A.
Inductive param_impred_ind (A : Prop) : Set :=
  mk_param_impred : A -> (forall X : Set, X) -> param_impred_ind A.
