From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Import Z.
Unset Lia Cache.

Goal forall (x y : Z),
   implb (Z.eqb x y) (Z.eqb y x) = true.
Proof.
  intros.
  lia.
Qed.

Goal forall (x y :Z), implb (Z.eqb x 0) (Z.eqb y 0) = true <->
                      orb (negb (Z.eqb x 0))(Z.eqb y 0) = true.
Proof.
  intro.
  lia.
Qed.
