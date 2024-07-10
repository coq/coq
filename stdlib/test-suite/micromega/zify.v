From Stdlib Require Import BinNums BinInt BinNat ZifyInst Zify.

Definition pos := positive.

Goal forall (x : pos), x = x.
Proof.
  intros.
  zify_op.
  apply (@eq_refl Z).
Qed.

Goal (1 <= Pos.to_nat 1)%nat.
Proof.
  zify_op.
  apply Z.le_refl.
Qed.

Goal forall (x : positive), not (x = x) -> False.
Proof.
  intros. zify_op.
  apply H.
  apply (@eq_refl Z).
Qed.

Goal (0 <= 0)%nat.
Proof.
  intros.
  zify_op.
  apply Z.le_refl.
Qed.


Lemma N : forall x, (0 <= Z.of_nat x)%Z.
Proof.
  intros.
  zify. exact cstr.
Defined.

Lemma N_eq : N =
fun x : nat => let cstr : (0 <= Z.of_nat x)%Z := Znat.Nat2Z.is_nonneg x in cstr.
Proof.
  reflexivity.
Qed.

Goal (Z.of_nat 1 * 0 = 0)%Z.
Proof.
  intros.
  zify.
  match goal with
  | |- (1 * 0 = 0)%Z => reflexivity
  end.
Qed.

Lemma  C : forall p,
  Z.pos p~1 = Z.pos p~1.
Proof.
  intros.
  zify_op.
  reflexivity.
Defined.

Lemma C_eq : C = fun p : positive =>
let cstr : (0 < Z.pos p)%Z := Pos2Z.pos_is_pos p in eq_refl.
Proof.
reflexivity.
Qed.


Goal forall p,
  (Z.pos p~1 = 2 * Z.pos p + 1)%Z.
Proof.
  intros.
  zify_op.
  reflexivity.
Qed.

Goal forall z,
    (2 * z = 2 * z)%Z.
Proof.
  intros.
  zify_op.
  reflexivity.
Qed.

Goal  (-1= Z.opp 1)%Z.
Proof.
  intros.
  zify_op.
  reflexivity.
Qed.

Goal forall x, Z.of_N (Pos.Nsucc_double x) = (2 * Z.of_N x + 1)%Z.
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x, Z.of_N (Pos.Ndouble x) = (2 * Z.of_N x)%Z.
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x, Z.of_N (N.succ_double x) = (2 * Z.of_N x + 1)%Z.
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x, Z.of_N (N.double x) = (2 * Z.of_N x)%Z.
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x, Z.pos (N.succ_pos x) = (Z.of_N x + 1)%Z.
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x, Z.of_N (N.div2 x) = (Z.of_N x / 2)%Z.
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x y, Z.of_N (N.pow x y) = (Z.pow (Z.of_N x) (Z.of_N y))%Z.
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x, Z.of_N (N.square x) = (Z.of_N x * Z.of_N x)%Z.
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x, Z.pos (Z.to_pos x) = Z.max 1 x.
Proof.
  intros; zify_op; reflexivity.
Qed.

From Stdlib Require Import Lia.

Goal forall n n3,
S n + n3 >= 0 + n.
Proof.
  intros.
  lia.
Qed.

Goal forall n, Nat.double n = n + n.
Proof. lia. Qed.

Open Scope Z_scope.

Goal forall n, Z.of_nat (Nat.div2 n) = Z.of_nat n / 2.
Proof. lia. Qed.

Goal forall p,
    False ->
    (Pos.to_nat p)  = 0%nat.
Proof.
  intros.
  zify_op.
  match goal with
  | H : False |- Z.pos p = Z0 => tauto
  end.
Qed.

Goal   forall
    fibonacci
    (p : positive)
    (n : nat)
    (b : Z)
    (H : 0%nat = (S (Pos.to_nat p) - n)%nat)
    (H0 : 0 < Z.pos p < b)
    (H1 : Z.pos p < fibonacci (S n)),
  Z.abs (Z.pos p) < Z.of_nat n.
Proof.
  intros.
  lia.
Qed.



Section S.
  Variable digits : positive.
  Hypothesis digits_ne_1 : digits <> 1%positive.

  Lemma spec_more_than_1_digit : (1 < Z.pos digits)%Z.
  Proof. lia. Qed.

  Let digits_gt_1 := spec_more_than_1_digit.

  Goal True.
  Proof.
    intros.
    zify.
    exact I.
  Qed.

End S.


Record Bla : Type :=
  mk
    {
      T : Type;
      zero : T
    }.

Definition znat := mk nat 0%nat.

From Stdlib Require Import ZifyClasses.
From Stdlib Require Import ZifyInst.

#[export] Instance Zero : CstOp (@zero znat : nat) := Op_O.
Add Zify CstOp Zero.


Goal  @zero znat = 0%nat.
  zify.
  reflexivity.
Qed.

Goal forall (x y : positive) (F : forall (P: Pos.le x y) , positive) (P : Pos.le x y),
    (F P + 1 = 1 + F P)%positive.
Proof.
  intros.
  zify_op.
  apply Z.add_comm.
Qed.

Goal forall (x y : nat) (F : forall (P: le x y) , nat) (P : le x y),
    (F P + 1 = 1 + F P)%nat.
Proof.
  intros.
  zify_op.
  apply Z.add_comm.
Qed.

From Stdlib Require Import Bool.

Goal true && false = false.
Proof.
  lia.
Qed.

Goal forall p, p || true   = true.
Proof.
  lia.
Qed.

Goal forall x y, Z.eqb x y = true -> x = y.
Proof.
  intros.
  lia.
Qed.

Goal forall x, Z.leb x x = true.
Proof.
  intros.
  lia.
Qed.

Goal forall x, Z.gtb x x = false.
Proof.
  intros.
  lia.
Qed.

From Stdlib Require Import ZifyBool.

#[export] Instance Op_bool_inj : UnOp (inj : bool -> bool) :=
  { TUOp := id; TUOpInj := fun _ => eq_refl }.
Add Zify UnOp Op_bool_inj.

Goal forall x y : nat, Nat.eqb x 1 = true ->
                       Nat.eqb y 0 = true ->
                       Nat.eqb (x + y) 1 = true.
Proof.
  intros x y.
  lia.
Qed.

Goal forall (f : Z -> bool), negb (negb (f 0)) = f 0.
Proof.
  intros. lia.
Qed.


Ltac Zify.zify_pre_hook ::= unfold is_true in *.

Goal forall x y : nat, is_true (Nat.eqb x 1) ->
                       is_true (Nat.eqb y 0) ->
                       is_true (Nat.eqb (x + y) 1).
Proof.
lia.
Qed.

Goal forall x y, Pos.eqb x y = Z.eqb (Z.pos x) (Z.pos y).
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x y, Pos.leb x y = Z.leb (Z.pos x) (Z.pos y).
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x y, Pos.ltb x y = Z.ltb (Z.pos x) (Z.pos y).
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x y, N.eqb x y = Z.eqb (Z.of_N x) (Z.of_N y).
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x y, N.leb x y = Z.leb (Z.of_N x) (Z.of_N y).
Proof.
  intros; zify_op; reflexivity.
Qed.

Goal forall x y, N.ltb x y = Z.ltb (Z.of_N x) (Z.of_N y).
Proof.
  intros; zify_op; reflexivity.
Qed.
