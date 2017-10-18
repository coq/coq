Set Primitive Projections.
Require Import ZArith ssreflect.

Module Test1.

Structure semigroup := SemiGroup {
  sg_car :> Type;
  sg_op : sg_car -> sg_car -> sg_car;
}.

Structure monoid := Monoid {
  monoid_car :> Type;
  monoid_op : monoid_car -> monoid_car -> monoid_car;
  monoid_unit : monoid_car;
}.

Coercion monoid_sg (X : monoid) : semigroup :=
  SemiGroup (monoid_car X) (monoid_op X).
Canonical Structure monoid_sg.

Parameter X : monoid.
Parameter x y : X.

Check (sg_op _ x y).

End Test1.

Module Test2.

Structure semigroup := SemiGroup {
  sg_car :> Type;
  sg_op : sg_car -> sg_car -> sg_car;
}.

Structure monoid := Monoid {
  monoid_car :> Type;
  monoid_op : monoid_car -> monoid_car -> monoid_car;
  monoid_unit : monoid_car;
  monoid_left_id x : monoid_op monoid_unit x = x;
}.

Coercion monoid_sg (X : monoid) : semigroup :=
  SemiGroup (monoid_car X) (monoid_op X).
Canonical Structure monoid_sg.

Canonical Structure nat_sg := SemiGroup nat plus.
Canonical Structure nat_monoid := Monoid nat plus 0 plus_O_n.

Lemma foo (x : nat) : 0 + x = x.
Proof.
apply monoid_left_id.
Qed.

End Test2.

Module Test3.

Structure semigroup := SemiGroup {
  sg_car :> Type;
  sg_op : sg_car -> sg_car -> sg_car;
}.

Structure group := Something {
  group_car :> Type;
  group_op : group_car -> group_car -> group_car;
  group_neg : group_car -> group_car;
  group_neg_op' x y : group_neg (group_op x y) = group_op (group_neg x) (group_neg y)
}.

Coercion group_sg (X : group) : semigroup :=
  SemiGroup (group_car X) (group_op X).
Canonical Structure group_sg.

Axiom group_neg_op : forall (X : group) (x y : X),
  group_neg X (sg_op (group_sg X) x y) = sg_op (group_sg X) (group_neg X x) (group_neg X y).

Canonical Structure Z_sg := SemiGroup Z Z.add .
Canonical Structure Z_group := Something Z Z.add Z.opp Z.opp_add_distr.

Lemma foo (x y : Z) :
  sg_op Z_sg (group_neg Z_group x) (group_neg Z_group y) =
  group_neg Z_group (sg_op Z_sg x y).
Proof.
  rewrite -group_neg_op.
  reflexivity.
Qed.

End Test3.
