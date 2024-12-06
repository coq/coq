(* bug 13242 *)

From Stdlib Require Import Lia.
Fail Add Zify InjTyp id.

(* bug 14054 *)

From Stdlib Require Import ZArith. Open Scope Z_scope.
From Stdlib.Init Require Byte.
From Stdlib.Strings Require Byte.
From Stdlib Require Import ZifyClasses Lia.

Notation byte := Stdlib.Init.Byte.byte.

Module byte.
  Definition unsigned(b: byte): Z := Z.of_N (Byte.to_N b).
End byte.

Section WithA.
  Context (A: Type).
  Fixpoint tuple(n: nat): Type :=
    match n with
    | O => unit
    | S m => A * tuple m
    end.
End WithA.

Module LittleEndian.
  Fixpoint combine (n : nat) : forall (bs : tuple byte n), Z :=
    match n with
    | O => fun _ => 0
    | S n => fun bs => Z.lor (byte.unsigned (fst bs))
                             (Z.shiftl (combine n (snd bs)) 8)
    end.
  Lemma combine_bound: forall {n: nat} (t: tuple byte n),
      0 <= LittleEndian.combine n t < 2 ^ (8 * Z.of_nat n).
  Admitted.
End LittleEndian.

#[export] Instance InjByteTuple{n: nat}: InjTyp (tuple byte n) Z := {|
  inj := LittleEndian.combine n;
  pred x := 0 <= x < 2 ^ (8 * Z.of_nat n);
  cstr := @LittleEndian.combine_bound n;
|}.
Fail Add Zify InjTyp InjByteTuple.
Fail Add Zify UnOp InjByteTuple.
Fail Add Zify UnOp X.
