Require Import ssreflect.

Section foo.

Variable A : Type.

Record bar (X : Type) := mk_bar {
  a : X * A;
  b : A;
  c := (a,7);
  _ : X;
  _ : X
}.

Inductive baz (X : Type) (Y : Type) : nat -> Type :=
| K1 x (e : 0=1) (f := 3) of x=x:>X : baz X Y O
| K2 n of n=n & baz X nat 0 : baz X Y (n+1).

Axiom Q : nat -> Prop.
Axiom Qx : forall x, Q x.
Axiom my_ind :
  forall P : nat -> Prop, P O -> (forall n m (w : P n /\ P m), P (n+m)) ->
     forall w, P w.

Lemma test x : bar nat -> baz nat nat x -> forall n : nat, Q n.
Proof.

(* record *)
move => [^~ _ccc ].
Check (refl_equal _ : c_ccc = (a_ccc, 7)).

(* inductive *)
move=> [^ xxx_ ].
Check (refl_equal _ : xxx_f = 3).
  by [].
Check (refl_equal _ : xxx_n = xxx_n).

(* eliminator *)
elim/my_ind => [^ wow_ ].
  exact: Qx 0.
Check (wow_w : Q wow_n /\ Q wow_m).
exact: Qx (wow_n + wow_m).

Qed.

Arguments mk_bar A x y z w : rename.
Arguments K1 A B a b c : rename.


Lemma test2 x : bar nat -> baz nat nat x -> forall n : nat, Q n.
Proof.
move=> [^~ _ccc ].
Check (refl_equal _ :  c_ccc = (x_ccc, 7)).
move=> [^ xxx_ ].
Check (refl_equal _ : xxx_f = 3).
  by [].
Check (refl_equal _ : xxx_n = xxx_n).
Abort.

End foo.
