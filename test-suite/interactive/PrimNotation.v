(* Until recently, the Notation.declare_numeral_notation wasn't synchronized
   w.r.t. backtracking. This should be ok now.
   This test is pretty artificial (we must declare Z_scope for this to work).
*)

Delimit Scope Z_scope with Z.
Open Scope Z_scope.
Check let v := 0 in v : nat.
(* let v := 0 in v : nat : nat *)
Require BinInt.
Check let v := 0 in v : BinNums.Z.
(* let v := 0 in v : BinNums.Z : BinNums.Z *)
Back 2.
Check let v := 0 in v : nat.
(* Expected answer: let v := 0 in v : nat : nat *)
(* Used to fail with:
Error: Cannot interpret in Z_scope without requiring first module BinNums.
*)

Local Set Universe Polymorphism.
Delimit Scope punit_scope with punit.
Delimit Scope pcunit_scope with pcunit.
Delimit Scope int_scope with int.
Numeral Notation Decimal.int Decimal.int_of_int Decimal.int_of_int : int_scope.
Module A.
  NonCumulative Inductive punit@{u} : Type@{u} := ptt.
  Cumulative Inductive pcunit@{u} : Type@{u} := pctt.
  Definition to_punit : Decimal.int -> option punit
    := fun v => match v with 0%int => Some ptt | _ => None end.
  Definition to_pcunit : Decimal.int -> option pcunit
    := fun v => match v with 0%int => Some pctt | _ => None end.
  Definition of_punit : punit -> Decimal.uint := fun _ => Nat.to_uint 0.
  Definition of_pcunit : pcunit -> Decimal.uint := fun _ => Nat.to_uint 0.
  Numeral Notation punit to_punit of_punit : punit_scope.
  Check let v := 0%punit in v : punit.
  Back 2.
  Numeral Notation pcunit to_pcunit of_pcunit : punit_scope.
  Check let v := 0%punit in v : pcunit.
End A.
Reset A.
Local Unset Universe Polymorphism.
Module A.
  Inductive punit : Set := ptt.
  Definition to_punit : Decimal.int -> option punit
    := fun v => match v with 0%int => Some ptt | _ => None end.
  Definition of_punit : punit -> Decimal.uint := fun _ => Nat.to_uint 0.
  Numeral Notation punit to_punit of_punit : punit_scope.
  Check let v := 0%punit in v : punit.
End A.
Local Set Universe Polymorphism.
Inductive punit@{u} : Type@{u} := ptt.
Definition to_punit : Decimal.int -> option punit
  := fun v => match v with 0%int => Some ptt | _ => None end.
Definition of_punit : punit -> Decimal.uint := fun _ => Nat.to_uint 0.
Numeral Notation punit to_punit of_punit : punit_scope.
Check let v := 0%punit in v : punit.
Back 6. (* check backtracking of registering universe polymorphic constants *)
Local Unset Universe Polymorphism.
Inductive punit : Set := ptt.
Definition to_punit : Decimal.int -> option punit
  := fun v => match v with 0%int => Some ptt | _ => None end.
Definition of_punit : punit -> Decimal.uint := fun _ => Nat.to_uint 0.
Numeral Notation punit to_punit of_punit : punit_scope.
Check let v := 0%punit in v : punit.
