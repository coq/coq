
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
