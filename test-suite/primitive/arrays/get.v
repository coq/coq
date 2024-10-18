From Stdlib Require Import PrimInt63 PrimArray.

Open Scope array_scope.

(* Test reduction of primitives on array with kernel conversion, vm_compute,
native_compute, cbv, cbn *)

(* Immediate values *)
Definition t : array nat := [| 1; 3; 2 | 4 |].
Definition foo1 := (eq_refl : t.[0] = 1).
Definition foo2 := (eq_refl 1 <: t.[0] = 1).
Definition foo3 := (eq_refl 1 <<: t.[0] = 1).
Definition x1 := Eval compute in t.[0].
Definition foo4 := (eq_refl : x1 = 1).
Definition x2 := Eval cbn in t.[0].
Definition foo5 := (eq_refl : x2 = 1).

Definition foo6 := (eq_refl : t.[2] = 2).
Definition foo7 := (eq_refl 2 <: t.[2] = 2).
Definition foo8 := (eq_refl 2 <<: t.[2] = 2).
Definition x3 := Eval compute in t.[2].
Definition foo9 := (eq_refl : x3 = 2).
Definition x4 := Eval cbn in t.[2].
Definition foo10 := (eq_refl : x4 = 2).

Definition foo11 := (eq_refl : t.[99] = 4).
Definition foo12 := (eq_refl 4 <: t.[99] = 4).
Definition foo13 := (eq_refl 4 <<: t.[99] = 4).
Definition x5 := Eval compute in t.[4].
Definition foo14 := (eq_refl : x5 = 4).
Definition x6 := Eval cbn in t.[4].
Definition foo15 := (eq_refl : x6 = 4).

(* Computations inside the array *)
Definition t2 : array nat := [| 1 + 3 | 5 |].
Definition foo16 := (eq_refl : t2.[0] = 4).
Definition foo17 := (eq_refl 4 <: t2.[0] = 4).
Definition foo18 := (eq_refl 4 <<: t2.[0] = 4).
Definition x7 := Eval compute in t2.[0].
Definition foo19 := (eq_refl : x7 = 4).
Definition x8 := Eval cbn in t2.[0].
Definition foo20 := (eq_refl : x8 = 4).

(* Functions inside the array *)
Definition t3 : array (nat -> nat) := [| fun x => x | fun x => O |].
Definition foo21 := (eq_refl : t3.[0] 2 = 2).
Definition foo22 := (eq_refl 2 <: t3.[0] 2 = 2).
Definition foo23 := (eq_refl 2 <<: t3.[0] 2 = 2).
Definition x9 := Eval compute in t3.[0] 2.
Definition foo24 := (eq_refl : x9 = 2).
Definition x10 := Eval cbn in t3.[0] 2.
Definition foo25 := (eq_refl : x10 = 2).

Ltac check_const_eq name constr :=
  let v := (eval cbv delta [name] in name) in
  tryif constr_eq v constr
  then idtac
  else fail 0 "Not syntactically equal:" name ":=" v "<>" constr.

Notation check_const_eq name constr := (ltac:(check_const_eq name constr; exact constr)) (only parsing).

(* Stuck primitive *)
Definition lazy_stuck_get := Eval lazy in (fun A (t : array A) => t.[0]).
Definition vm_stuck_get := Eval vm_compute in (fun A (t : array A) => t.[0]).
Definition native_stuck_get := Eval native_compute in (fun A (t : array A) => t.[0]).
Definition compute_stuck_get := Eval compute in (fun A (t : array A) => t.[0]).
Definition cbn_stuck_get := Eval cbn in (fun A (t : array A) => t.[0]).

Check check_const_eq lazy_stuck_get (fun A (t : array A) => t.[0]).
Check check_const_eq vm_stuck_get (fun A (t : array A) => t.[0]).
Check check_const_eq native_stuck_get (fun A (t : array A) => t.[0]).
Check check_const_eq compute_stuck_get (fun A (t : array A) => t.[0]).
Check check_const_eq cbn_stuck_get (fun A (t : array A) => t.[0]).

(* Under-application *)
Definition lazy_get := Eval lazy in @PrimArray.get.
Definition vm_get := Eval vm_compute in @PrimArray.get.
Definition native_get := Eval native_compute in @PrimArray.get.
Definition compute_get := Eval compute in @PrimArray.get.
Definition cbn_get := Eval cbn in @PrimArray.get.

Check check_const_eq lazy_get (@PrimArray.get).
Check check_const_eq vm_get (fun A (t : array A) i => t.[i]).
Check check_const_eq native_get (fun A (t : array A) i => t.[i]).
Check check_const_eq compute_get (@PrimArray.get).
Check check_const_eq cbn_get (@PrimArray.get).
