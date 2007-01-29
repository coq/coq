Require Import Rdefinitions.

Fixpoint pow (r:R) (n:nat) {struct n} : R :=
  match n with
    | O => R1
    | S n => Rmult r (pow r n)
  end.
