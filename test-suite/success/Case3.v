Inductive Le : nat -> nat -> Set :=
  | LeO : forall n : nat, Le 0 n
  | LeS : forall n m : nat, Le n m -> Le (S n) (S m).

Parameter discr_l : forall n : nat, S n <> 0.

Type
  (fun n : nat =>
   match n return (n = 0 \/ n <> 0) with
   | O => or_introl (0 <> 0) (refl_equal 0)
   | S O => or_intror (1 = 0) (discr_l 0)
   | S (S x) => or_intror (S (S x) = 0) (discr_l (S x))
   end).

Parameter iguales : forall (n m : nat) (h : Le n m), Prop.

Type
  match LeO 0 as h in (Le n m) return Prop with
  | LeO O => True
  | LeS (S x) (S y) H => iguales (S x) (S y) H
  | _ => False
  end.

Type
  match LeO 0 as h in (Le n m) return Prop with
  | LeO O => True
  | LeS (S x) O H => iguales (S x) 0 H
  | _ => False
  end.
