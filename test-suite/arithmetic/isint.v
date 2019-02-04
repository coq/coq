(* This file tests the check that arithmetic operations use to know if their
arguments are ground. The various test cases correspond to possible
optimizations of these tests made by the compiler. *)
Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Section test.

Variable m n : int.

Check (eq_refl : (fun x => x + 3) m = m + 3).
Check (eq_refl (m + 3) <: (fun x => x + 3) m = m + 3).
Check (eq_refl (m + 3) <<: (fun x => x + 3) m = m + 3).
Definition compute1 := Eval compute in (fun x => x + 3) m.
Check (eq_refl compute1 : m + 3 = m + 3).

Check (eq_refl : (fun x => 3 + x) m = 3 + m).
Check (eq_refl (3 + m) <: (fun x => 3 + x) m = 3 + m).
Check (eq_refl (3 + m) <<: (fun x => 3 + x) m = 3 + m).
Definition compute2 := Eval compute in (fun x => 3 + x) m.
Check (eq_refl compute2 : 3 + m = 3 + m).

Check (eq_refl : (fun x y => x + y) m n = m + n).
Check (eq_refl (m + n) <: (fun x y => x + y) m n = m + n).
Check (eq_refl (m + n) <<: (fun x y => x + y) m n = m + n).
Definition compute3 := Eval compute in (fun x y => x + y) m n.
Check (eq_refl compute3 : m + n = m + n).

Check (eq_refl : (fun x y => x + y) 2 3 = 5).
Check (eq_refl 5 <: (fun x y => x + y) 2 3 = 5).
Check (eq_refl 5 <<: (fun x y => x + y) 2 3 = 5).
Definition compute4 := Eval compute in (fun x y => x + y) 2 3.
Check (eq_refl compute4 : 5 = 5).

Check (eq_refl : (fun x => x + x) m = m + m).
Check (eq_refl (m + m) <: (fun x => x + x) m = m + m).
Check (eq_refl (m + m) <<: (fun x => x + x) m = m + m).
Definition compute5 := Eval compute in (fun x => x + x) m.
Check (eq_refl compute5 : m + m = m + m).

Check (eq_refl : (fun x => x + x) 2 = 4).
Check (eq_refl 4 <: (fun x => x + x) 2 = 4).
Check (eq_refl 4 <<: (fun x => x + x) 2 = 4).
Definition compute6 := Eval compute in (fun x => x + x) 2.
Check (eq_refl compute6 : 4 = 4).

End test.
