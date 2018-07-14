
(* Test that we fail, rather than raising anomalies, on opaque terms during interpretation *)

(* https://github.com/coq/coq/pull/8064#discussion_r202497516 *)
Module Test1.
  Axiom hold : forall {A B C}, A -> B -> C.
  Definition opaque3 (x : Decimal.int) : Decimal.int := hold x (fix f (x : nat) : nat := match x with O => O | S n => S (f n) end).
  Numeral Notation Decimal.int opaque3 opaque3 : opaque_scope.
  Delimit Scope opaque_scope with opaque.
  Fail Check 1%opaque.
End Test1.

(* https://github.com/coq/coq/pull/8064#discussion_r202497990 *)
Module Test2.
  Axiom opaque4 : option Decimal.int.
  Definition opaque6 (x : Decimal.int) : option Decimal.int := opaque4.
  Numeral Notation Decimal.int opaque6 opaque6 : opaque_scope.
  Delimit Scope opaque_scope with opaque.
  Open Scope opaque_scope.
  Fail Check 1%opaque.
End Test2.

Module Test3.
  Inductive silly := SILLY (v : Decimal.uint) (f : forall A, A -> A).
  Definition to_silly (v : Decimal.uint) := SILLY v (fun _ x => x).
  Definition of_silly (v : silly) := match v with SILLY v _ => v end.
  Numeral Notation silly to_silly of_silly : silly_scope.
  Delimit Scope silly_scope with silly.
  Fail Check 1%silly.
End Test3.


Module Test4.
  Polymorphic Inductive punit := ptt.
  Polymorphic Definition pto_punit (v : Decimal.uint) : option punit := match Nat.of_uint v with O => Some ptt | _ => None end.
  Polymorphic Definition pof_punit (v : punit) : Decimal.uint := Nat.to_uint 0.
  Definition to_punit (v : Decimal.uint) : option punit := match Nat.of_uint v with O => Some ptt | _ => None end.
  Definition of_punit (v : punit) : Decimal.uint := Nat.to_uint 0.
  Polymorphic Definition pto_unit (v : Decimal.uint) : option unit := match Nat.of_uint v with O => Some tt | _ => None end.
  Polymorphic Definition pof_unit (v : unit) : Decimal.uint := Nat.to_uint 0.
  Definition to_unit (v : Decimal.uint) : option unit := match Nat.of_uint v with O => Some tt | _ => None end.
  Definition of_unit (v : unit) : Decimal.uint := Nat.to_uint 0.
  Fail Numeral Notation punit to_punit of_punit : pto.
  Fail Numeral Notation punit pto_punit of_punit : ppo.
  Fail Numeral Notation punit to_punit pof_punit : ptp.
  Fail Numeral Notation punit pto_punit pof_punit : ppp.
  Numeral Notation unit to_unit of_unit : uto.
  Delimit Scope uto with uto.
  Check let v := 0%uto in v : unit.
  Fail Check 1%uto.
  Fail Check (-1)%uto.
  Fail Numeral Notation unit pto_unit of_unit : upo.
  Fail Numeral Notation unit to_unit pof_unit : utp.
  Fail Numeral Notation unit pto_unit pof_unit : upp.
End Test4.
