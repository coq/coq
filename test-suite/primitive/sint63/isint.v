(* This file tests the check that arithmetic operations use to know if their
arguments are ground. The various test cases correspond to possible
optimizations of these tests made by the compiler. *)
Require Import TestSuite.sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Section test.

Variable m n : int.

Check (eq_refl : (fun x => add x 3) m = add m 3).
Check (eq_refl (add m 3) <: (fun x => add x 3) m = add m 3).
Check (eq_refl (add m 3) <<: (fun x => add x 3) m = add m 3).
Definition compute1 := Eval compute in (fun x => add x 3) m.
Check (eq_refl compute1 : add m 3 = add m 3).

Check (eq_refl : (fun x => add 3 x) m = add 3 m).
Check (eq_refl (add 3 m) <: (fun x => add 3 x) m = add 3 m).
Check (eq_refl (add 3 m) <<: (fun x => add 3 x) m = add 3 m).
Definition compute2 := Eval compute in (fun x => add 3 x) m.
Check (eq_refl compute2 : add 3 m = add 3 m).

Check (eq_refl : (fun x y => add x y) m n = add m n).
Check (eq_refl (add m n) <: (fun x y => add x y) m n = add m n).
Check (eq_refl (add m n) <<: (fun x y => add x y) m n = add m n).
Definition compute3 := Eval compute in (fun x y => add x y) m n.
Check (eq_refl compute3 : add m n = add m n).

Check (eq_refl : (fun x y => add x y) 2 3 = 5).
Check (eq_refl 5 <: (fun x y => add x y) 2 3 = 5).
Check (eq_refl 5 <<: (fun x y => add x y) 2 3 = 5).
Definition compute4 := Eval compute in (fun x y => add x y) 2 3.
Check (eq_refl compute4 : 5 = 5).

Check (eq_refl : (fun x => add x x) m = add m m).
Check (eq_refl (add m m) <: (fun x => add x x) m = add m m).
Check (eq_refl (add m m) <<: (fun x => add x x) m = add m m).
Definition compute5 := Eval compute in (fun x => add x x) m.
Check (eq_refl compute5 : add m m = add m m).

Check (eq_refl : (fun x => add x x) 2 = 4).
Check (eq_refl 4 <: (fun x => add x x) 2 = 4).
Check (eq_refl 4 <<: (fun x => add x x) 2 = 4).
Definition compute6 := Eval compute in (fun x => add x x) 2.
Check (eq_refl compute6 : 4 = 4).

End test.
