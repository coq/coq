(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**********************************************************************)
(** * Binary positive numbers, operations *)
(**********************************************************************)

(** Initial development by Pierre Crégut, CNET, Lannion, France *)

(** The type [positive] and its constructors [xI] and [xO] and [xH]
    are now defined in [BinNums.v] *)

From Stdlib Require Export BinNums.

Local Open Scope positive_scope.

(** Postfix notation for positive numbers, which allows mimicking
    the position of bits in a big-endian representation.
    For instance, we can write [1~1~0] instead of [(xO (xI xH))]
    for the number 6 (which is 110 in binary notation).
*)

Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope.
Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

Notation "1" := xH : positive_scope.
Notation "2" := 1~0 : positive_scope.
Notation "3" := 1~1 : positive_scope.

Module Pos.

(** * Operations over positive numbers *)

(** ** Successor *)

Fixpoint succ x :=
  match x with
    | p~1 => (succ p)~0
    | p~0 => p~1
    | 1 => 1~0
  end.

(** ** Addition *)

Fixpoint add x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~0
    | p~1, q~0 => (add p q)~1
    | p~1, 1 => (succ p)~0
    | p~0, q~1 => (add p q)~1
    | p~0, q~0 => (add p q)~0
    | p~0, 1 => p~1
    | 1, q~1 => (succ q)~0
    | 1, q~0 => q~1
    | 1, 1 => 1~0
  end

with add_carry x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~1
    | p~1, q~0 => (add_carry p q)~0
    | p~1, 1 => (succ p)~1
    | p~0, q~1 => (add_carry p q)~0
    | p~0, q~0 => (add p q)~1
    | p~0, 1 => (succ p)~0
    | 1, q~1 => (succ q)~1
    | 1, q~0 => (succ q)~0
    | 1, 1 => 1~1
  end.

(** ** Operation [x -> 2*x-1] *)

Fixpoint pred_double x :=
  match x with
    | p~1 => p~0~1
    | p~0 => (pred_double p)~1
    | 1 => 1
  end.

(** ** The predecessor of a positive number can be seen as a [N] *)

Definition pred_N x :=
  match x with
    | p~1 => Npos (p~0)
    | p~0 => Npos (pred_double p)
    | 1 => N0
  end.

(** ** An auxiliary type for subtraction *)

Inductive mask : Set :=
| IsNul : mask
| IsPos : positive -> mask
| IsNeg : mask.

(** ** Operation [x -> 2*x+1] *)

Definition succ_double_mask (x:mask) : mask :=
  match x with
    | IsNul => IsPos 1
    | IsNeg => IsNeg
    | IsPos p => IsPos p~1
  end.

(** ** Operation [x -> 2*x] *)

Definition double_mask (x:mask) : mask :=
  match x with
    | IsNul => IsNul
    | IsNeg => IsNeg
    | IsPos p => IsPos p~0
  end.

(** ** Operation [x -> 2*x-2] *)

Definition double_pred_mask x : mask :=
  match x with
    | p~1 => IsPos p~0~0
    | p~0 => IsPos (pred_double p)~0
    | 1 => IsNul
  end.

(** ** Subtraction, result as a mask *)

Fixpoint sub_mask (x y:positive) {struct y} : mask :=
  match x, y with
    | p~1, q~1 => double_mask (sub_mask p q)
    | p~1, q~0 => succ_double_mask (sub_mask p q)
    | p~1, 1 => IsPos p~0
    | p~0, q~1 => succ_double_mask (sub_mask_carry p q)
    | p~0, q~0 => double_mask (sub_mask p q)
    | p~0, 1 => IsPos (pred_double p)
    | 1, 1 => IsNul
    | 1, _ => IsNeg
  end

with sub_mask_carry (x y:positive) {struct y} : mask :=
  match x, y with
    | p~1, q~1 => succ_double_mask (sub_mask_carry p q)
    | p~1, q~0 => double_mask (sub_mask p q)
    | p~1, 1 => IsPos (pred_double p)
    | p~0, q~1 => double_mask (sub_mask_carry p q)
    | p~0, q~0 => succ_double_mask (sub_mask_carry p q)
    | p~0, 1 => double_pred_mask p
    | 1, _ => IsNeg
  end.

(** ** Subtraction, result as a positive, returning 1 if [x<=y] *)

Definition sub x y :=
  match sub_mask x y with
    | IsPos z => z
    | _ => 1
  end.

(** ** Multiplication *)

Fixpoint mul x y :=
  match x with
    | p~1 => add y (mul p y)~0
    | p~0 => (mul p y)~0
    | 1 => y
  end.

(** ** Iteration over a positive number *)

Definition iter {A} (f:A -> A) : A -> positive -> A :=
  fix iter_fix x n := match n with
    | xH => f x
    | xO n' => iter_fix (iter_fix x n') n'
    | xI n' => f (iter_fix (iter_fix x n') n')
  end.

(** ** Division by 2 rounded below but for 1 *)

Definition div2 p :=
  match p with
    | 1 => 1
    | p~0 => p
    | p~1 => p
  end.

(** Division by 2 rounded up *)

Definition div2_up p :=
 match p with
   | 1 => 1
   | p~0 => p
   | p~1 => succ p
 end.

(** ** Comparison on binary positive numbers *)

Fixpoint compare_cont (r:comparison) (x y:positive) {struct y} : comparison :=
  match x, y with
    | p~1, q~1 => compare_cont r p q
    | p~1, q~0 => compare_cont Gt p q
    | p~1, 1 => Gt
    | p~0, q~1 => compare_cont Lt p q
    | p~0, q~0 => compare_cont r p q
    | p~0, 1 => Gt
    | 1, q~1 => Lt
    | 1, q~0 => Lt
    | 1, 1 => r
  end.

Definition compare := compare_cont Eq.

(** ** Boolean equality and comparisons *)

Fixpoint eqb p q {struct q} :=
  match p, q with
    | p~1, q~1 => eqb p q
    | p~0, q~0 => eqb p q
    | 1, 1 => true
    | _, _ => false
  end.

Definition leb x y :=
 match compare x y with Gt => false | _ => true end.

(** ** A Square Root function for positive numbers *)

(** We proceed by blocks of two digits : if p is written qbb'
    then sqrt(p) will be sqrt(q)~0 or sqrt(q)~1.
    For deciding easily in which case we are, we store the remainder
    (as a mask, since it can be null).
    Instead of copy-pasting the following code four times, we
    factorize as an auxiliary function, with f and g being either
    xO or xI depending of the initial digits.
    NB: (sub_mask (g (f 1)) 4) is a hack, morally it's g (f 0).
*)

Definition sqrtrem_step (f g:positive->positive) p :=
 match p with
  | (s, IsPos r) =>
    let s' := s~0~1 in
    let r' := g (f r) in
    if leb s' r' then (s~1, sub_mask r' s')
    else (s~0, IsPos r')
  | (s,_)  => (s~0, sub_mask (g (f 1)) 1~0~0)
 end.

Fixpoint sqrtrem p : positive * mask :=
 match p with
  | 1 => (1,IsNul)
  | 1~0 => (1,IsPos 1)
  | 1~1 => (1,IsPos 1~0)
  | p~0~0 => sqrtrem_step xO xO (sqrtrem p)
  | p~0~1 => sqrtrem_step xO xI (sqrtrem p)
  | p~1~0 => sqrtrem_step xI xO (sqrtrem p)
  | p~1~1 => sqrtrem_step xI xI (sqrtrem p)
 end.

Definition sqrt p := fst (sqrtrem p).

Definition Nsucc_double x :=
  match x with
  | N0 => Npos 1
  | Npos p => Npos p~1
  end.

Definition Ndouble n :=
  match n with
  | N0 => N0
  | Npos p => Npos p~0
  end.

(** Operation over bits. *)

(** Logical [or] *)

Fixpoint lor (p q : positive) : positive :=
  match p, q with
    | 1, q~0 => q~1
    | 1, _ => q
    | p~0, 1 => p~1
    | _, 1 => p
    | p~0, q~0 => (lor p q)~0
    | p~0, q~1 => (lor p q)~1
    | p~1, q~0 => (lor p q)~1
    | p~1, q~1 => (lor p q)~1
  end.

(** Logical [and] *)

Fixpoint land (p q : positive) : N :=
  match p, q with
    | 1, q~0 => N0
    | 1, _ => Npos 1
    | p~0, 1 => N0
    | _, 1 => Npos 1
    | p~0, q~0 => Ndouble (land p q)
    | p~0, q~1 => Ndouble (land p q)
    | p~1, q~0 => Ndouble (land p q)
    | p~1, q~1 => Nsucc_double (land p q)
  end.

(** Logical [diff] *)

Fixpoint ldiff (p q:positive) : N :=
  match p, q with
    | 1, q~0 => Npos 1
    | 1, _ => N0
    | _~0, 1 => Npos p
    | p~1, 1 => Npos (p~0)
    | p~0, q~0 => Ndouble (ldiff p q)
    | p~0, q~1 => Ndouble (ldiff p q)
    | p~1, q~1 => Ndouble (ldiff p q)
    | p~1, q~0 => Nsucc_double (ldiff p q)
  end.

(** [xor] *)

Fixpoint lxor (p q:positive) : N :=
  match p, q with
    | 1, 1 => N0
    | 1, q~0 => Npos (q~1)
    | 1, q~1 => Npos (q~0)
    | p~0, 1 => Npos (p~1)
    | p~0, q~0 => Ndouble (lxor p q)
    | p~0, q~1 => Nsucc_double (lxor p q)
    | p~1, 1 => Npos (p~0)
    | p~1, q~0 => Nsucc_double (lxor p q)
    | p~1, q~1 => Ndouble (lxor p q)
  end.

(** ** From binary positive numbers to Peano natural numbers *)

Definition iter_op {A}(op:A->A->A) :=
  fix iter (p:positive)(a:A) : A :=
  match p with
    | 1 => a
    | p~0 => iter p (op a a)
    | p~1 => op a (iter p (op a a))
  end.

Definition to_nat (x:positive) : nat := iter_op plus x (S O).
Arguments to_nat x: simpl never.

(** ** From Peano natural numbers to binary positive numbers *)

(* A version that converts [n] into [n+1] *)

Fixpoint of_succ_nat (n:nat) : positive :=
  match n with
    | O => 1
    | S x => succ (of_succ_nat x)
  end.

End Pos.
