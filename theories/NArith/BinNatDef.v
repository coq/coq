(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export BinNums.
Require Import BinPos.

Local Open Scope N_scope.

(**********************************************************************)
(** * Binary natural numbers, definitions of operations *)
(**********************************************************************)

Module N.

Definition t := N.

(** ** Constants *)

Definition zero := 0.
Definition one := 1.
Definition two := 2.

(** ** Operation [x -> 2*x+1] *)

Definition succ_double x :=
  match x with
  | 0 => 1
  | Npos p => Npos p~1
  end.

(** ** Operation [x -> 2*x] *)

Definition double n :=
  match n with
  | 0 => 0
  | Npos p => Npos p~0
  end.

(** ** Successor *)

Definition succ n :=
  match n with
  | 0 => 1
  | Npos p => Npos (Pos.succ p)
  end.

(** ** Predecessor *)

Definition pred n :=
  match n with
  | 0 => 0
  | Npos p => Pos.pred_N p
  end.

(** ** The successor of a [N] can be seen as a [positive] *)

Definition succ_pos (n : N) : positive :=
 match n with
   | N0 => 1%positive
   | Npos p => Pos.succ p
 end.

(** ** Addition *)

Definition add n m :=
  match n, m with
  | 0, _ => m
  | _, 0 => n
  | Npos p, Npos q => Npos (p + q)
  end.

Infix "+" := add : N_scope.

(** Subtraction *)

Definition sub n m :=
match n, m with
| 0, _ => 0
| n, 0 => n
| Npos n', Npos m' =>
  match Pos.sub_mask n' m' with
  | IsPos p => Npos p
  | _ => 0
  end
end.

Infix "-" := sub : N_scope.

(** Multiplication *)

Definition mul n m :=
  match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | Npos p, Npos q => Npos (p * q)
  end.

Infix "*" := mul : N_scope.

(** Order *)

Definition compare n m :=
  match n, m with
  | 0, 0 => Eq
  | 0, Npos m' => Lt
  | Npos n', 0 => Gt
  | Npos n', Npos m' => (n' ?= m')%positive
  end.

Infix "?=" := compare (at level 70, no associativity) : N_scope.

(** Boolean equality and comparison *)

(** Nota: this [eqb] is not convertible with the generated [N_beq],
    since the underlying [Pos.eqb] differs from [positive_beq]
    (cf BinIntDef). *)

Fixpoint eqb n m :=
  match n, m with
    | 0, 0 => true
    | Npos p, Npos q => Pos.eqb p q
    | _, _ => false
  end.

Definition leb x y :=
 match x ?= y with Gt => false | _ => true end.

Definition ltb x y :=
 match x ?= y with Lt => true | _ => false end.

Infix "=?" := eqb (at level 70, no associativity) : N_scope.
Infix "<=?" := leb (at level 70, no associativity) : N_scope.
Infix "<?" := ltb (at level 70, no associativity) : N_scope.

(** Min and max *)

Definition min n n' := match n ?= n' with
 | Lt | Eq => n
 | Gt => n'
 end.

Definition max n n' := match n ?= n' with
 | Lt | Eq => n'
 | Gt => n
 end.

(** Dividing by 2 *)

Definition div2 n :=
  match n with
  | 0 => 0
  | 1 => 0
  | Npos (p~0) => Npos p
  | Npos (p~1) => Npos p
  end.

(** Parity *)

Definition even n :=
  match n with
    | 0 => true
    | Npos (xO _) => true
    | _ => false
  end.

Definition odd n := negb (even n).

(** Power *)

Definition pow n p :=
  match p, n with
    | 0, _ => 1
    | _, 0 => 0
    | Npos p, Npos q => Npos (q^p)
  end.

Infix "^" := pow : N_scope.

(** Base-2 logarithm *)

Definition log2 n :=
 match n with
   | 0 => 0
   | 1 => 0
   | Npos (p~0) => Npos (Pos.size p)
   | Npos (p~1) => Npos (Pos.size p)
 end.

(** How many digits in a number ?
    Number 0 is said to have no digits at all.
*)

Definition size n :=
 match n with
  | 0 => 0
  | Npos p => Npos (Pos.size p)
 end.

Definition size_nat n :=
 match n with
  | 0 => O
  | Npos p => Pos.size_nat p
 end.

(** Euclidean division *)

Fixpoint pos_div_eucl (a:positive)(b:N) : N * N :=
  match a with
    | xH =>
       match b with 1 => (1,0) | _ => (0,1) end
    | xO a' =>
       let (q, r) := pos_div_eucl a' b in
       let r' := double r in
       if b <=? r' then (succ_double q, r' - b)
        else (double q, r')
    | xI a' =>
       let (q, r) := pos_div_eucl a' b in
       let r' := succ_double r in
       if b <=? r' then (succ_double q, r' - b)
        else  (double q, r')
  end.

Definition div_eucl (a b:N) : N * N :=
  match a, b with
   | 0,  _ => (0, 0)
   | _, 0  => (0, a)
   | Npos na, _ => pos_div_eucl na b
  end.

Definition div a b := fst (div_eucl a b).
Definition modulo a b := snd (div_eucl a b).

Infix "/" := div : N_scope.
Infix "mod" := modulo (at level 40, no associativity) : N_scope.

(** Greatest common divisor *)

Definition gcd a b :=
 match a, b with
  | 0, _ => b
  | _, 0 => a
  | Npos p, Npos q => Npos (Pos.gcd p q)
 end.

(** Generalized Gcd, also computing rests of [a] and [b] after
    division by gcd. *)

Definition ggcd a b :=
 match a, b with
  | 0, _ => (b,(0,1))
  | _, 0 => (a,(1,0))
  | Npos p, Npos q =>
     let '(g,(aa,bb)) := Pos.ggcd p q in
     (Npos g, (Npos aa, Npos bb))
 end.

(** Square root *)

Definition sqrtrem n :=
 match n with
  | 0 => (0, 0)
  | Npos p =>
    match Pos.sqrtrem p with
     | (s, IsPos r) => (Npos s, Npos r)
     | (s, _) => (Npos s, 0)
    end
 end.

Definition sqrt n :=
 match n with
  | 0 => 0
  | Npos p => Npos (Pos.sqrt p)
 end.

(** Operation over bits of a [N] number. *)

(** Logical [or] *)

Definition lor n m :=
 match n, m with
   | 0, _ => m
   | _, 0 => n
   | Npos p, Npos q => Npos (Pos.lor p q)
 end.

(** Logical [and] *)

Definition land n m :=
 match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | Npos p, Npos q => Pos.land p q
 end.

(** Logical [diff] *)

Fixpoint ldiff n m :=
 match n, m with
  | 0, _ => 0
  | _, 0 => n
  | Npos p, Npos q => Pos.ldiff p q
 end.

(** [xor] *)

Definition lxor n m :=
  match n, m with
    | 0, _ => m
    | _, 0 => n
    | Npos p, Npos q => Pos.lxor p q
  end.

(** Shifts *)

Definition shiftl_nat (a:N)(n:nat) := nat_iter n double a.
Definition shiftr_nat (a:N)(n:nat) := nat_iter n div2 a.

Definition shiftl a n :=
  match a with
    | 0 => 0
    | Npos a => Npos (Pos.shiftl a n)
  end.

Definition shiftr a n :=
  match n with
    | 0 => a
    | Npos p => Pos.iter p div2 a
  end.

(** Checking whether a particular bit is set or not *)

Definition testbit_nat (a:N) :=
  match a with
    | 0 => fun _ => false
    | Npos p => Pos.testbit_nat p
  end.

(** Same, but with index in N *)

Definition testbit a n :=
  match a with
    | 0 => false
    | Npos p => Pos.testbit p n
  end.

(** Translation from [N] to [nat] and back. *)

Definition to_nat (a:N) :=
  match a with
    | 0 => O
    | Npos p => Pos.to_nat p
  end.

Definition of_nat (n:nat) :=
  match n with
    | O => 0
    | S n' => Npos (Pos.of_succ_nat n')
  end.

(** Iteration of a function *)

Definition iter (n:N) {A} (f:A->A) (x:A) : A :=
  match n with
    | 0 => x
    | Npos p => Pos.iter p f x
  end.

End N.