From Stdlib Require Import PrimInt63 PrimArray.

Open Scope array_scope.

Definition t : array nat := [| 1; 3; 2 | 4 |].
Definition t' : array nat := t.[1 <- 5].

Definition foo1 := (eq_refl : t'.[1] = 5).
Definition foo2 := (eq_refl 5 <: t'.[1] = 5).
Definition foo3 := (eq_refl 5 <<: t'.[1] = 5).
Definition x1 := Eval compute in t'.[1].
Definition foo4 := (eq_refl : x1 = 5).
Definition x2 := Eval cbn in t'.[1].
Definition foo5 := (eq_refl : x2 = 5).

Definition foo6 := (eq_refl : t.[1] = 3).
Definition foo7 := (eq_refl 3 <: t.[1] = 3).
Definition foo8 := (eq_refl 3 <<: t.[1] = 3).
Definition x3 := Eval compute in t.[1].
Definition foo9 := (eq_refl : x3 = 3).
Definition x4 := Eval cbn in t.[1].
Definition foo10 := (eq_refl : x4 = 3).

Ltac check_const_eq name constr :=
  let v := (eval cbv delta [name] in name) in
  tryif constr_eq v constr
  then idtac
  else fail 0 "Not syntactically equal:" name ":=" v "<>" constr.

Notation check_const_eq name constr := (ltac:(check_const_eq name constr; exact constr)) (only parsing).

(* Stuck primitive *)
Definition lazy_stuck_set := Eval lazy in (fun A (t : array A) v => t.[1 <- v]).
Definition vm_stuck_set := Eval vm_compute in (fun A (t : array A) v => t.[1 <- v]).
Definition native_stuck_set := Eval native_compute in (fun A (t : array A) v => t.[1 <- v]).
Definition compute_stuck_set := Eval compute in (fun A (t : array A) v => t.[1 <- v]).
Definition cbn_stuck_set := Eval cbn in (fun A (t : array A) v => t.[1 <- v]).

Check check_const_eq lazy_stuck_set (fun A (t : array A) v => t.[1 <- v]).
Check check_const_eq vm_stuck_set (fun A (t : array A) v => t.[1 <- v]).
Check check_const_eq native_stuck_set (fun A (t : array A) v => t.[1 <- v]).
Check check_const_eq compute_stuck_set (fun A (t : array A) v => t.[1 <- v]).
Check check_const_eq cbn_stuck_set (fun A (t : array A) v => t.[1 <- v]).

(* Not stuck primitive, but with an accumulator as last argument *)
Definition lazy_accu_set := Eval lazy in (fun v => t.[1 <- v]).
Definition vm_accu_set := Eval vm_compute in (fun v => t.[1 <- v]).
Definition native_accu_set := Eval native_compute in (fun v => t.[1 <- v]).
Definition compute_accu_set := Eval compute in (fun v => t.[1 <- v]).
Definition cbn_accu_set := Eval cbn in (fun v => t.[1 <- v]).

Check check_const_eq lazy_accu_set (fun v => [| 1; v; 2 | 4 |]).
Check check_const_eq vm_accu_set (fun v => [| 1; v; 2 | 4 |]).
Check check_const_eq native_accu_set (fun v => [| 1; v; 2 | 4 |]).
Check check_const_eq compute_accu_set (fun v => [| 1; v; 2 | 4 |]).
Check check_const_eq cbn_accu_set (fun v => [| 1; v; 2 | 4 |]).

(* Under-application *)
Definition lazy_set := Eval lazy in @PrimArray.set.
Definition vm_set := Eval vm_compute in @PrimArray.set.
Definition native_set := Eval native_compute in @PrimArray.set.
Definition compute_set := Eval compute in @PrimArray.set.
Definition cbn_set := Eval cbn in @PrimArray.set.

Check check_const_eq lazy_set (@PrimArray.set).
Check check_const_eq vm_set (fun A (t : array A) i v => t.[i <- v]).
Check check_const_eq native_set (fun A (t : array A) i v => t.[i <- v]).
Check check_const_eq compute_set (@PrimArray.set).
Check check_const_eq cbn_set (@PrimArray.set).
