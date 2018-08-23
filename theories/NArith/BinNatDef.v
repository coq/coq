(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export BinNums.
Require Import BinPos.

Local Open Scope N_scope.

Local Notation "0" := N0.
Local Notation "1" := (Npos 1).
Local Notation "2" := (Npos 2).

(**********************************************************************)
(** * Binary natural numbers, definitions of operations *)
(**********************************************************************)

Module N.

Definition t := N.

(** ** Nicer name [N.pos] for contructor [Npos] *)

Notation pos := Npos.

(** ** Constants *)

Definition zero := 0.
Definition one := 1.
Definition two := 2.

(** ** Operation [x -> 2*x+1] *)

Definition succ_double x :=
  match x with
  | 0 => 1
  | pos p => pos p~1
  end.

(** ** Operation [x -> 2*x] *)

Definition double n :=
  match n with
  | 0 => 0
  | pos p => pos p~0
  end.

(** ** Successor *)

Definition succ n :=
  match n with
  | 0 => 1
  | pos p => pos (Pos.succ p)
  end.

(** ** Predecessor *)

Definition pred n :=
  match n with
  | 0 => 0
  | pos p => Pos.pred_N p
  end.

(** ** The successor of a [N] can be seen as a [positive] *)

Definition succ_pos (n : N) : positive :=
 match n with
   | 0 => 1%positive
   | pos p => Pos.succ p
 end.

(** ** Addition *)

Definition add n m :=
  match n, m with
  | 0, _ => m
  | _, 0 => n
  | pos p, pos q => pos (p + q)
  end.

Infix "+" := add : N_scope.

(** Subtraction *)

Definition sub n m :=
match n, m with
| 0, _ => 0
| n, 0 => n
| pos n', pos m' =>
  match Pos.sub_mask n' m' with
  | IsPos p => pos p
  | _ => 0
  end
end.

Infix "-" := sub : N_scope.

(** Multiplication *)

Definition mul n m :=
  match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | pos p, pos q => pos (p * q)
  end.

Infix "*" := mul : N_scope.

(** Order *)

Definition compare n m :=
  match n, m with
  | 0, 0 => Eq
  | 0, pos m' => Lt
  | pos n', 0 => Gt
  | pos n', pos m' => (n' ?= m')%positive
  end.

Infix "?=" := compare (at level 70, no associativity) : N_scope.

(** Boolean equality and comparison *)

Fixpoint eqb n m :=
  match n, m with
    | 0, 0 => true
    | pos p, pos q => Pos.eqb p q
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
  | pos (p~0) => pos p
  | pos (p~1) => pos p
  end.

(** Parity *)

Definition even n :=
  match n with
    | 0 => true
    | pos (xO _) => true
    | _ => false
  end.

Definition odd n := negb (even n).

(** Power *)

Definition pow n p :=
  match p, n with
    | 0, _ => 1
    | _, 0 => 0
    | pos p, pos q => pos (q^p)
  end.

Infix "^" := pow : N_scope.

(** Square *)

Definition square n :=
  match n with
    | 0 => 0
    | pos p => pos (Pos.square p)
  end.

(** Base-2 logarithm *)

Definition log2 n :=
 match n with
   | 0 => 0
   | 1 => 0
   | pos (p~0) => pos (Pos.size p)
   | pos (p~1) => pos (Pos.size p)
 end.

(** How many digits in a number ?
    Number 0 is said to have no digits at all.
*)

Definition size n :=
 match n with
  | 0 => 0
  | pos p => pos (Pos.size p)
 end.

Definition size_nat n :=
 match n with
  | 0 => O
  | pos p => Pos.size_nat p
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
   | pos na, _ => pos_div_eucl na b
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
  | pos p, pos q => pos (Pos.gcd p q)
 end.

(** Generalized Gcd, also computing rests of [a] and [b] after
    division by gcd. *)

Definition ggcd a b :=
 match a, b with
  | 0, _ => (b,(0,1))
  | _, 0 => (a,(1,0))
  | pos p, pos q =>
     let '(g,(aa,bb)) := Pos.ggcd p q in
     (pos g, (pos aa, pos bb))
 end.

(** Square root *)

Definition sqrtrem n :=
 match n with
  | 0 => (0, 0)
  | pos p =>
    match Pos.sqrtrem p with
     | (s, IsPos r) => (pos s, pos r)
     | (s, _) => (pos s, 0)
    end
 end.

Definition sqrt n :=
 match n with
  | 0 => 0
  | pos p => pos (Pos.sqrt p)
 end.

(** Operation over bits of a [N] number. *)

(** Logical [or] *)

Definition lor n m :=
 match n, m with
   | 0, _ => m
   | _, 0 => n
   | pos p, pos q => pos (Pos.lor p q)
 end.

(** Logical [and] *)

Definition land n m :=
 match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | pos p, pos q => Pos.land p q
 end.

(** Logical [diff] *)

Fixpoint ldiff n m :=
 match n, m with
  | 0, _ => 0
  | _, 0 => n
  | pos p, pos q => Pos.ldiff p q
 end.

(** [xor] *)

Definition lxor n m :=
  match n, m with
    | 0, _ => m
    | _, 0 => n
    | pos p, pos q => Pos.lxor p q
  end.

(** Shifts *)

Definition shiftl_nat (a:N) := nat_rect _ a (fun _ => double).
Definition shiftr_nat (a:N) := nat_rect _ a (fun _ => div2).

Definition shiftl a n :=
  match a with
    | 0 => 0
    | pos a => pos (Pos.shiftl a n)
  end.

Definition shiftr a n :=
  match n with
    | 0 => a
    | pos p => Pos.iter div2 a p
  end.

(** Checking whether a particular bit is set or not *)

Definition testbit_nat (a:N) :=
  match a with
    | 0 => fun _ => false
    | pos p => Pos.testbit_nat p
  end.

(** Same, but with index in N *)

Definition testbit a n :=
  match a with
    | 0 => false
    | pos p => Pos.testbit p n
  end.

(** Translation from [N] to [nat] and back. *)

Definition to_nat (a:N) :=
  match a with
    | 0 => O
    | pos p => Pos.to_nat p
  end.

Definition of_nat (n:nat) :=
  match n with
    | O => 0
    | S n' => pos (Pos.of_succ_nat n')
  end.

(** Iteration of a function *)

Definition iter (n:N) {A} (f:A->A) (x:A) : A :=
  match n with
    | 0 => x
    | pos p => Pos.iter f x p
  end.

(** Conversion with a decimal representation for printing/parsing *)

Definition of_uint (d:Decimal.uint) := Pos.of_uint d.

Definition of_int (d:Decimal.int) :=
  match Decimal.norm d with
  | Decimal.Pos d => Some (Pos.of_uint d)
  | Decimal.Neg _ => None
  end.

Definition to_uint n :=
  match n with
  | 0 => Decimal.zero
  | pos p => Pos.to_uint p
  end.

Definition to_int n := Decimal.Pos (to_uint n).

Numeral Notation N of_uint to_uint : N_scope.

End N.

(** Re-export the notation for those who just [Import NatIntDef] *)
Numeral Notation N N.of_uint N.to_uint : N_scope.
