Record TYPE := Pack_TYPE { sort_TYPE :> Type }.
Record eqType := Pack_eq { sort_eq :> Type; _ : sort_eq -> sort_eq -> bool }.

Definition eq_op (T : eqType) : T -> T -> bool :=
  match T with Pack_eq _ op => op end.

Definition bool_eqb b1 b2 :=
  match b1, b2 with
  | false, false => true
  | true, true => true
  | _, _ => false
  end.

Canonical bool_TYPE := Pack_TYPE bool.
Canonical bool_eqType := Pack_eq bool bool_eqb.

Canonical nat_TYPE := Pack_TYPE nat.
Canonical nat_eqType := Pack_eq nat Nat.eqb.

Definition prod_eqb (T U : eqType) (x y : T * U) :=
  match x, y with
  | (x1, x2), (y1, y2) =>
    andb (eq_op _ x1 y1) (eq_op _ x2 y2)
  end.

Canonical prod_TYPE (T U : TYPE) := Pack_TYPE (T * U).
Canonical prod_eqType (T U : eqType) := Pack_eq (T * U) (prod_eqb T U).

Definition sum_eqb (T U : eqType) (x y : T + U) :=
  match x, y with
  | inl x, inl y => eq_op _ x y
  | inr x, inr y => eq_op _ x y
  | _, _ => false
  end.

Canonical sum_TYPE (T U : TYPE) := Pack_TYPE (T + U).
Canonical sum_eqType (T U : eqType) := Pack_eq (T + U) (sum_eqb T U).

Print Canonical Projections bool.
Print Canonical Projections nat.
Print Canonical Projections prod.
Print Canonical Projections sum.
Print Canonical Projections sort_TYPE.
Print Canonical Projections sort_eq.
Print Canonical Projections sort_TYPE bool.
Print Canonical Projections bool_eqType.
