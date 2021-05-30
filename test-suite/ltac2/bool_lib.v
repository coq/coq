Require Import Ltac2.Ltac2.
Require Import Ltac2.Bool.


(** * Lazy eval tests *)

Require Import Ltac2.Notations.

(** ** Lazy and tests *)

Example lazy_and_true_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true && true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_true_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (true && false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_false_throw : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (false && Control.throw_invalid_argument "bad") then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_true_true_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true && true && true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_true_false_throw : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (true && false && Control.throw_invalid_argument "bad") then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_false_throw_throw : exists n, n=0.
Proof.
  (* This shows that && is left recursive *)
  exists ltac2:(let val:= if (false && Control.throw_invalid_argument "bad" && Control.throw_invalid_argument "bad") then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_fun_arg : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (Bool.equal true true && Bool.equal false false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

(** ** Lazy or tests *)

Example lazy_or_false_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (false || false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_false_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (false || true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_true_throw : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true || Control.throw_invalid_argument "bad") then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_false_false_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (false || false || false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_false_true_throw : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (false || true || Control.throw_invalid_argument "bad") then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_true_throw_throw : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true || Control.throw_invalid_argument "bad" || Control.throw_invalid_argument "bad") then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_fun_arg : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (Bool.equal true true || Bool.equal true false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

(** ** Lazy or with and tests *)

Example lazy_or_and_true_true_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true || true && true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_and_true_true_false : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true || true && false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_and_true_false_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true || false && true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_and_true_false_false : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true || false && false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_and_false_true_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (false || true && true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_and_false_true_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (false || true && false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_and_false_false_true : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (false || false && true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_and_false_false_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (false || false && false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

(* Lazy and with or tests *)

Example lazy_and_or_true_true_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true && true || true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_or_true_true_false : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true && true || false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_or_true_false_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (true && false || true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_or_true_false_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (true && false || false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_or_false_true_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (false && true || true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_or_false_true_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (false && true || false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_or_false_false_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if (false && false || true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_or_false_false_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if (false && false || false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

(** * if then else tests *)

(* these tests are from teh time when if was a notation, but it doesn't hurt to keep them *)

Example if_then_else_true : exists n, n=1.
Proof.
  exists ltac2:(let val:=if true then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_false : exists n, n=0.
Proof.
  exists ltac2:(let val:=if false then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_nested_true : exists n, n=2.
Proof.
  exists ltac2:(let val:=if true then if true then '2 else '1 else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_nested_false : exists n, n=0.
Proof.
  exists ltac2:(let val:=if false then '2 else if false then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_match_cond : exists n, n=0.
Proof.
  exists ltac2:(let val:=if match true with true => false | false => true end then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_match_true : exists n, n=2.
Proof.
  exists ltac2:(let val:=if true then match true with true => '2 | false => '1 end else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_match_false : exists n, n=0.
Proof.
  exists ltac2:(let val:=if false then '2 else match false with true => '1 | false => '0 end in exact $val).
  reflexivity.
Qed.

Example if_then_else_lazy_and : exists n, n=1.
Proof.
  exists ltac2:(let val:=if true && true then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_lazy_or : exists n, n=1.
Proof.
  exists ltac2:(let val:=if true || true then '1 else '0 in exact $val).
  reflexivity.
Qed.
