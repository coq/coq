(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

Require Export BinNums BinNums.PosDef.

Local Open Scope positive_scope.

Module Pos.

Include BinNums.PosDef.Pos.

Definition t := positive.

(** * Operations over positive numbers *)

Infix "+" := add : positive_scope.

(** ** Predecessor *)

Definition pred x :=
  match x with
    | p~1 => p~0
    | p~0 => pred_double p
    | 1 => 1
  end.

(** ** Predecessor with mask *)

Definition pred_mask (p : mask) : mask :=
  match p with
    | IsPos 1 => IsNul
    | IsPos q => IsPos (pred q)
    | IsNul => IsNeg
    | IsNeg => IsNeg
  end.

Infix "-" := sub : positive_scope.

Infix "*" := mul : positive_scope.

(** ** Power *)

Definition pow (x:positive) := iter (mul x) 1.

Infix "^" := pow : positive_scope.

(** ** Square *)

Fixpoint square p :=
  match p with
    | p~1 => (square p + p)~0~1
    | p~0 => (square p)~0~0
    | 1 => 1
  end.

(** ** Number of digits in a positive number *)

Fixpoint size_nat p : nat :=
  match p with
    | 1 => S O
    | p~1 => S (size_nat p)
    | p~0 => S (size_nat p)
  end.

(** Same, with positive output *)

Fixpoint size p :=
  match p with
    | 1 => 1
    | p~1 => succ (size p)
    | p~0 => succ (size p)
  end.

Infix "?=" := compare (at level 70, no associativity) : positive_scope.

Definition min p p' :=
 match p ?= p' with
 | Lt | Eq => p
 | Gt => p'
 end.

Definition max p p' :=
 match p ?= p' with
 | Lt | Eq => p'
 | Gt => p
 end.

(** ** Boolean equality and comparisons *)

Definition ltb x y :=
 match x ?= y with Lt => true | _ => false end.

Infix "=?" := eqb (at level 70, no associativity) : positive_scope.
Infix "<=?" := leb (at level 70, no associativity) : positive_scope.
Infix "<?" := ltb (at level 70, no associativity) : positive_scope.

(** ** Greatest Common Divisor *)

Definition divide p q := exists r, q = r*p.
Notation "( p | q )" := (divide p q) (at level 0) : positive_scope.

(** Instead of the Euclid algorithm, we use here the Stein binary
   algorithm, which is faster for this representation. This algorithm
   is almost structural, but in the last cases we do some recursive
   calls on subtraction, hence the need for a counter.
*)

Fixpoint gcdn (n : nat) (a b : positive) : positive :=
  match n with
    | O => 1
    | S n =>
      match a,b with
        | 1, _ => 1
        | _, 1 => 1
        | a~0, b~0 => (gcdn n a b)~0
        | _  , b~0 => gcdn n a b
        | a~0, _   => gcdn n a b
        | a'~1, b'~1 =>
          match a' ?= b' with
            | Eq => a
            | Lt => gcdn n (b'-a') a
            | Gt => gcdn n (a'-b') b
          end
      end
  end.

(** We'll show later that we need at most (log2(a.b)) loops *)

Definition gcd (a b : positive) := gcdn (size_nat a + size_nat b)%nat a b.

(** Generalized Gcd, also computing the division of a and b by the gcd *)
Set Printing Universes.
Fixpoint ggcdn (n : nat) (a b : positive) : (positive*(positive*positive)) :=
  match n with
    | O => (1,(a,b))
    | S n =>
      match a,b with
        | 1, _ => (1,(1,b))
        | _, 1 => (1,(a,1))
        | a~0, b~0 =>
           let (g,p) := ggcdn n a b in
           (g~0,p)
        | _, b~0 =>
           let '(g,(aa,bb)) := ggcdn n a b in
           (g,(aa, bb~0))
        | a~0, _ =>
           let '(g,(aa,bb)) := ggcdn n a b in
           (g,(aa~0, bb))
        | a'~1, b'~1 =>
           match a' ?= b' with
             | Eq => (a,(1,1))
             | Lt =>
                let '(g,(ba,aa)) := ggcdn n (b'-a') a in
                (g,(aa, aa + ba~0))
             | Gt =>
                let '(g,(ab,bb)) := ggcdn n (a'-b') b in
                (g,(bb + ab~0, bb))
           end
      end
  end.

Definition ggcd (a b: positive) := ggcdn (size_nat a + size_nat b)%nat a b.

(** Shifts. NB: right shift of 1 stays at 1. *)

Definition shiftl_nat (p:positive) := nat_rect _ p (fun _ => xO).
Definition shiftr_nat (p:positive) := nat_rect _ p (fun _ => div2).

Definition shiftl (p:positive)(n:N) :=
  match n with
    | N0 => p
    | Npos n => iter xO p n
  end.

Definition shiftr (p:positive)(n:N) :=
  match n with
    | N0 => p
    | Npos n => iter div2 p n
  end.

(** Checking whether a particular bit is set or not *)

Fixpoint testbit_nat (p:positive) : nat -> bool :=
  match p with
    | 1 => fun n => match n with
                      | O => true
                      | S _ => false
                    end
    | p~0 => fun n => match n with
                        | O => false
                        | S n' => testbit_nat p n'
                      end
    | p~1 => fun n => match n with
                        | O => true
                        | S n' => testbit_nat p n'
                      end
  end.

(** Same, but with index in N *)

Fixpoint testbit (p:positive)(n:N) :=
  match p, n with
    | p~0, N0 => false
    | _, N0 => true
    | 1, _ => false
    | p~0, Npos n => testbit p (pred_N n)
    | p~1, Npos n => testbit p (pred_N n)
  end.

(** ** From Peano natural numbers to binary positive numbers *)

(** A version preserving positive numbers, and sending 0 to 1. *)

Fixpoint of_nat (n:nat) : positive :=
 match n with
   | O => 1
   | S O => 1
   | S x => succ (of_nat x)
 end.

(** ** Conversion with a decimal representation for printing/parsing *)

Local Notation ten := 1~0~1~0.

Fixpoint of_uint_acc (d:Decimal.uint)(acc:positive) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 l => of_uint_acc l (mul ten acc)
  | Decimal.D1 l => of_uint_acc l (add 1 (mul ten acc))
  | Decimal.D2 l => of_uint_acc l (add 1~0 (mul ten acc))
  | Decimal.D3 l => of_uint_acc l (add 1~1 (mul ten acc))
  | Decimal.D4 l => of_uint_acc l (add 1~0~0 (mul ten acc))
  | Decimal.D5 l => of_uint_acc l (add 1~0~1 (mul ten acc))
  | Decimal.D6 l => of_uint_acc l (add 1~1~0 (mul ten acc))
  | Decimal.D7 l => of_uint_acc l (add 1~1~1 (mul ten acc))
  | Decimal.D8 l => of_uint_acc l (add 1~0~0~0 (mul ten acc))
  | Decimal.D9 l => of_uint_acc l (add 1~0~0~1 (mul ten acc))
  end.

Fixpoint of_uint (d:Decimal.uint) : N :=
  match d with
  | Decimal.Nil => N0
  | Decimal.D0 l => of_uint l
  | Decimal.D1 l => Npos (of_uint_acc l 1)
  | Decimal.D2 l => Npos (of_uint_acc l 1~0)
  | Decimal.D3 l => Npos (of_uint_acc l 1~1)
  | Decimal.D4 l => Npos (of_uint_acc l 1~0~0)
  | Decimal.D5 l => Npos (of_uint_acc l 1~0~1)
  | Decimal.D6 l => Npos (of_uint_acc l 1~1~0)
  | Decimal.D7 l => Npos (of_uint_acc l 1~1~1)
  | Decimal.D8 l => Npos (of_uint_acc l 1~0~0~0)
  | Decimal.D9 l => Npos (of_uint_acc l 1~0~0~1)
  end.

Local Notation sixteen := 1~0~0~0~0.

Fixpoint of_hex_uint_acc (d:Hexadecimal.uint)(acc:positive) :=
  match d with
  | Hexadecimal.Nil => acc
  | Hexadecimal.D0 l => of_hex_uint_acc l (mul sixteen acc)
  | Hexadecimal.D1 l => of_hex_uint_acc l (add 1 (mul sixteen acc))
  | Hexadecimal.D2 l => of_hex_uint_acc l (add 1~0 (mul sixteen acc))
  | Hexadecimal.D3 l => of_hex_uint_acc l (add 1~1 (mul sixteen acc))
  | Hexadecimal.D4 l => of_hex_uint_acc l (add 1~0~0 (mul sixteen acc))
  | Hexadecimal.D5 l => of_hex_uint_acc l (add 1~0~1 (mul sixteen acc))
  | Hexadecimal.D6 l => of_hex_uint_acc l (add 1~1~0 (mul sixteen acc))
  | Hexadecimal.D7 l => of_hex_uint_acc l (add 1~1~1 (mul sixteen acc))
  | Hexadecimal.D8 l => of_hex_uint_acc l (add 1~0~0~0 (mul sixteen acc))
  | Hexadecimal.D9 l => of_hex_uint_acc l (add 1~0~0~1 (mul sixteen acc))
  | Hexadecimal.Da l => of_hex_uint_acc l (add 1~0~1~0 (mul sixteen acc))
  | Hexadecimal.Db l => of_hex_uint_acc l (add 1~0~1~1 (mul sixteen acc))
  | Hexadecimal.Dc l => of_hex_uint_acc l (add 1~1~0~0 (mul sixteen acc))
  | Hexadecimal.Dd l => of_hex_uint_acc l (add 1~1~0~1 (mul sixteen acc))
  | Hexadecimal.De l => of_hex_uint_acc l (add 1~1~1~0 (mul sixteen acc))
  | Hexadecimal.Df l => of_hex_uint_acc l (add 1~1~1~1 (mul sixteen acc))
  end.

Fixpoint of_hex_uint (d:Hexadecimal.uint) : N :=
  match d with
  | Hexadecimal.Nil => N0
  | Hexadecimal.D0 l => of_hex_uint l
  | Hexadecimal.D1 l => Npos (of_hex_uint_acc l 1)
  | Hexadecimal.D2 l => Npos (of_hex_uint_acc l 1~0)
  | Hexadecimal.D3 l => Npos (of_hex_uint_acc l 1~1)
  | Hexadecimal.D4 l => Npos (of_hex_uint_acc l 1~0~0)
  | Hexadecimal.D5 l => Npos (of_hex_uint_acc l 1~0~1)
  | Hexadecimal.D6 l => Npos (of_hex_uint_acc l 1~1~0)
  | Hexadecimal.D7 l => Npos (of_hex_uint_acc l 1~1~1)
  | Hexadecimal.D8 l => Npos (of_hex_uint_acc l 1~0~0~0)
  | Hexadecimal.D9 l => Npos (of_hex_uint_acc l 1~0~0~1)
  | Hexadecimal.Da l => Npos (of_hex_uint_acc l 1~0~1~0)
  | Hexadecimal.Db l => Npos (of_hex_uint_acc l 1~0~1~1)
  | Hexadecimal.Dc l => Npos (of_hex_uint_acc l 1~1~0~0)
  | Hexadecimal.Dd l => Npos (of_hex_uint_acc l 1~1~0~1)
  | Hexadecimal.De l => Npos (of_hex_uint_acc l 1~1~1~0)
  | Hexadecimal.Df l => Npos (of_hex_uint_acc l 1~1~1~1)
  end.

Definition of_num_uint (d:Number.uint) : N :=
  match d with
  | Number.UIntDecimal d => of_uint d
  | Number.UIntHexadecimal d => of_hex_uint d
  end.

Definition of_int (d:Decimal.int) : option positive :=
  match d with
  | Decimal.Pos d =>
    match of_uint d with
    | N0 => None
    | Npos p => Some p
    end
  | Decimal.Neg _ => None
  end.

Definition of_hex_int (d:Hexadecimal.int) : option positive :=
  match d with
  | Hexadecimal.Pos d =>
    match of_hex_uint d with
    | N0 => None
    | Npos p => Some p
    end
  | Hexadecimal.Neg _ => None
  end.

Definition of_num_int (d:Number.int) : option positive :=
  match d with
  | Number.IntDecimal d => of_int d
  | Number.IntHexadecimal d => of_hex_int d
  end.

Fixpoint to_little_uint p :=
  match p with
  | 1 => Decimal.D1 Decimal.Nil
  | p~1 => Decimal.Little.succ_double (to_little_uint p)
  | p~0 => Decimal.Little.double (to_little_uint p)
  end.

Definition to_uint p := Decimal.rev (to_little_uint p).

Fixpoint to_little_hex_uint p :=
  match p with
  | 1 => Hexadecimal.D1 Hexadecimal.Nil
  | p~1 => Hexadecimal.Little.succ_double (to_little_hex_uint p)
  | p~0 => Hexadecimal.Little.double (to_little_hex_uint p)
  end.

Definition to_hex_uint p := Hexadecimal.rev (to_little_hex_uint p).

Definition to_num_uint p := Number.UIntDecimal (to_uint p).

Definition to_num_hex_uint n := Number.UIntHexadecimal (to_hex_uint n).

Definition to_int n := Decimal.Pos (to_uint n).

Definition to_hex_int p := Hexadecimal.Pos (to_hex_uint p).

Definition to_num_int n := Number.IntDecimal (to_int n).

Definition to_num_hex_int n := Number.IntHexadecimal (to_hex_int n).

Number Notation positive of_num_int to_num_hex_uint : hex_positive_scope.
Number Notation positive of_num_int to_num_uint : positive_scope.

End Pos.

(** Re-export the notation for those who just [Import BinPosDef] *)
Number Notation positive Pos.of_num_int Pos.to_num_hex_uint : hex_positive_scope.
Number Notation positive Pos.of_num_int Pos.to_num_uint : positive_scope.
