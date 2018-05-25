
Inductive equivalent P Q := Equivalent (P_to_Q : P -> Q) (Q_to_P : Q -> P).

Inductive equal T (x : T) : T -> Type := Equal : equal T x x.

(* Arithmetic *)

Inductive natural := Zero | Add_1_to (n : natural).

Fixpoint add (m n : natural) : natural :=
  match m with Zero => n | Add_1_to m_minus_1 => add m_minus_1 (Add_1_to n) end.

Definition double (n : natural) : natural := add n n.

Inductive odd (n : natural) :=
  Odd (half : natural)
    (n_odd : equal natural n (Add_1_to (double half))).

Inductive less_than (m n : natural) :=
  LessThan (diff : natural)
    (m_lt_n : equal natural n (Add_1_to (add m diff))).

(* Finite subsets *)

Definition injective_in T R (D : T -> Type) (f : T -> R) :=
  forall x y, D x -> D y -> equal R (f x) (f y) -> equal T x y.

Inductive in_image T R (D : T -> Type) (f : T -> R) (a : R) :=
  InImage (x : T) (x_in_D : D x) (a_is_fx : equal R a (f x)).

Inductive finite_of_order T (D : T -> Type) (n : natural) :=
  FiniteOfOrder (rank : T -> natural)
    (rank_injective : injective_in T natural D rank)
    (rank_onto :
       forall i, equivalent (less_than i n) (in_image T natural D rank i)).

(* Constraints *)
Universes i j.
Inductive constraint1 : (Type -> Type) -> Type := mk_constraint1 : constraint1 (fun x : Type@{i} => (x : Type@{j})).
Constraint i < j.
Inductive constraint2 : Type@{j} := mkc2 (_ : Type@{i}).
Universes i' j'.
Constraint i' = j'.
Inductive constraint3 : (Type -> Type) -> Type := mk_constraint3 : constraint3 (fun x : Type@{i'} => (x : Type@{j'})).
Inductive constraint4 : (Type -> Type) -> Type
  := mk_constraint4 : let U1 := Type in
                      let U2 := Type in
                      constraint4 (fun x : U1 => (x : U2)).

Module CMP_CON.
  (* Comparison of opaque constants MUST be up to the universe graph.
     See #6798. *)
  Universe big.

  Polymorphic Lemma foo@{u} : Type@{big}.
  Proof. exact Type@{u}. Qed.

  Universes U V.

  Definition yo : foo@{U} = foo@{V} := eq_refl.
End CMP_CON.

Set Universe Polymorphism.

Module POLY_SUBTYP.

  Module Type T.
    Axiom foo : Type.
    Parameter bar@{u v|u = v} : foo@{u}.
  End T.

  Module M.
    Axiom foo : Type.
    Axiom bar@{u v|u = v} : foo@{v}.
  End M.

  Module F (A:T). End F.

  Module X := F M.

End POLY_SUBTYP.

Module POLY_IND.

  Polymorphic Inductive ind@{u v | u < v} : Prop := .

  Polymorphic Definition cst@{u v | v < u} := Prop.

End POLY_IND.
