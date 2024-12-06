(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export BinNums.
Require Import BinPos.
Require Export BinNums.NatDef.

Local Open Scope N_scope.

Local Notation "0" := N0.
Local Notation "1" := (Npos 1).
Local Notation "2" := (Npos 2).

(**********************************************************************)
(** * Binary natural numbers, definitions of operations *)
(**********************************************************************)

Module N.

Include BinNums.NatDef.N.

Definition t := N.

(** ** Nicer name [N.pos] for constructor [Npos] *)

Notation pos := Npos.

(** ** Constants *)

Definition zero := 0.
Definition one := 1.
Definition two := 2.

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

(** ** Addition *)

Definition add n m :=
  match n, m with
  | 0, _ => m
  | _, 0 => n
  | pos p, pos q => pos (p + q)
  end.

Infix "+" := add : N_scope.

Infix "-" := sub : N_scope.

(** Multiplication *)

Definition mul n m :=
  match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | pos p, pos q => pos (p * q)
  end.

Infix "*" := mul : N_scope.

Infix "?=" := compare (at level 70, no associativity) : N_scope.

(** Boolean equality and comparison *)

Definition eqb n m :=
  match n, m with
    | 0, 0 => true
    | pos p, pos q => Pos.eqb p q
    | _, _ => false
  end.

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

Definition of_hex_uint (d:Hexadecimal.uint) := Pos.of_hex_uint d.

Definition of_num_uint (d:Number.uint) :=
  match d with
  | Number.UIntDecimal d => of_uint d
  | Number.UIntHexadecimal d => of_hex_uint d
  end.

Definition of_int (d:Decimal.int) :=
  match Decimal.norm d with
  | Decimal.Pos d => Some (Pos.of_uint d)
  | Decimal.Neg _ => None
  end.

Definition of_hex_int (d:Hexadecimal.int) :=
  match Hexadecimal.norm d with
  | Hexadecimal.Pos d => Some (Pos.of_hex_uint d)
  | Hexadecimal.Neg _ => None
  end.

Definition of_num_int (d:Number.int) :=
  match d with
  | Number.IntDecimal d => of_int d
  | Number.IntHexadecimal d => of_hex_int d
  end.

Definition to_uint n :=
  match n with
  | 0 => Decimal.zero
  | pos p => Pos.to_uint p
  end.

Definition to_hex_uint n :=
  match n with
  | 0 => Hexadecimal.zero
  | pos p => Pos.to_hex_uint p
  end.

Definition to_num_uint n := Number.UIntDecimal (to_uint n).

Definition to_num_hex_uint n := Number.UIntHexadecimal (to_hex_uint n).

Definition to_int n := Decimal.Pos (to_uint n).

Definition to_hex_int n := Hexadecimal.Pos (to_hex_uint n).

Definition to_num_int n := Number.IntDecimal (to_int n).

Definition to_num_hex_int n := Number.IntHexadecimal (to_hex_int n).

Number Notation N of_num_uint to_num_hex_uint : hex_N_scope.
Number Notation N of_num_uint to_num_uint : N_scope.

End N.

(** Re-export the notation for those who just [Import NatIntDef] *)
Number Notation N N.of_num_uint N.to_num_hex_uint : hex_N_scope.
Number Notation N N.of_num_uint N.to_num_uint : N_scope.
