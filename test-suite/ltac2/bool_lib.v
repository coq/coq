Require Import Ltac2.Ltac2.
Require Import Ltac2.Bool.


(** * Lazy eval tests *)

Require Import Ltac2.Notations.

Example lazy_and_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if_bool (lazy_and false (Control.throw_invalid_argument "bad")) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_true_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if_bool (lazy_and true false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_and_true_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if_bool (lazy_and true true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if_bool (lazy_or true (Control.throw_invalid_argument "bad")) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_false_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if_bool (lazy_or false true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_or_false_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if_bool (lazy_or false false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_impl_false : exists n, n=1.
Proof.
  exists ltac2:(let val:= if_bool (lazy_impl false (Control.throw_invalid_argument "bad")) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_impl_true_false : exists n, n=0.
Proof.
  exists ltac2:(let val:= if_bool (lazy_impl true false) then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example lazy_impl_true_true : exists n, n=1.
Proof.
  exists ltac2:(let val:= if_bool (lazy_impl true true) then '1 else '0 in exact $val).
  reflexivity.
Qed.

(** * if then else tests *)

Example if_then_else_true : exists n, n=1.
Proof.
  exists ltac2:(let val:=if_bool true then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_false : exists n, n=0.
Proof.
  exists ltac2:(let val:=if_bool false then '1 else '0 in exact $val).
  reflexivity.
Qed.

(** Notes: parenthesis are mandatory for nested ifs - this is by design) *)

Example if_then_else_nested_true : exists n, n=2.
Proof.
  exists ltac2:(let val:=if_bool true then (if_bool true then '2 else '1) else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_nested_false : exists n, n=0.
Proof.
  exists ltac2:(let val:=if_bool false then '2 else (if_bool false then '1 else '0) in exact $val).
  reflexivity.
Qed.

Example if_then_else_match_cond : exists n, n=0.
Proof.
  exists ltac2:(let val:=if_bool match true with true => false | false => true end then '1 else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_match_true : exists n, n=2.
Proof.
  exists ltac2:(let val:=if_bool true then match true with true => '2 | false => '1 end else '0 in exact $val).
  reflexivity.
Qed.

Example if_then_else_match_false : exists n, n=0.
Proof.
  exists ltac2:(let val:=if_bool false then '2 else match false with true => '1 | false => '0 end in exact $val).
  reflexivity.
Qed.

(** * if then tests *)

Example if_then_true : 0=0.
Proof.
  if_bool true then reflexivity.
Qed.

Example if_then_false : 0=0.
Proof.
  if_bool false then reflexivity.
  reflexivity.
Qed.

Example if_then_sequence : 0=0.
Proof.
  (); if_bool false then reflexivity; reflexivity.
Qed.
