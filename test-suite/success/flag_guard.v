
(* Traversing Subterm Analysis *)

Module Subterm.

  Unset Guard Checking Option Traversing Subterm Analysis.

  (* Rec call on variables are still allowed *)
  Inductive lnat :=
  | lO : lnat
  | lS : lnat -> lnat.

  Fixpoint zero (n : lnat) : lnat :=
    match n with
    | lO => lO
    | lS x => zero x
    end.

  (* Same for Primtive Projections  *)
  Set Primitive Projections.

  Inductive RNat := {
    Rb : bool;
    RNatS : Rb = true -> RNat
  }.

  Fixpoint toNat (x : RNat) : nat :=
    match x.(Rb) as y return x.(Rb) = y -> nat with
    | false => fun e => 0
    | true => fun e => S (toNat (x.(RNatS) e))
    end eq_refl.

  (* subterm analysis going through fixpoint and match are now rejected *)
  Fail Fixpoint foo x y {struct x} : nat :=
    match x with
    | 0 => 0
    | S z => foo (z - y) y
    end.

  (* Whd is still on though *)
  Fixpoint id (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n => S (id ((fun x => x) n))
    end.

  (* [Unset Guard Checking] Keep the Options as is *)
  Unset Guard Checking.
  Set Guard Checking.
  Fail Fixpoint foo x y {struct x} : nat :=
    match x with
    | 0 => 0
    | S z => foo (z - y) y
    end.

  (* Accepted if the analysis is activated *)
  Set Guard Checking Option Traversing Subterm Analysis.

  Fixpoint foo x y {struct x} : nat :=
    match x with
    | 0 => 0
    | S z => foo (z - y) y
    end.

End Subterm.

(* Failure examples from the reference manual, with the default guard checks. *)
Module Refman.

  Fail Fixpoint wrongplus (n m : nat) {struct n} : nat :=
    match m with
    | 0 => n
    | S p => S (wrongplus n p)
    end.

  Definition id (n : nat) :=
    match n with
    | 0 => 0
    | S p => S p
    end.

  Fail Fixpoint zero_id (n : nat) : nat :=
    match n with
    | 0 => 0
    | S p => zero_id (id p)
    end.

End Refman.
