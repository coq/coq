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

Require Export BinNums.
Require Import BinPos BinNat.
Require Export BinNums.IntDef.

Local Open Scope Z_scope.

Local Notation "0" := Z0.
Local Notation "1" := (Zpos 1).
Local Notation "2" := (Zpos 2).

(***********************************************************)
(** * Binary Integers, Definitions of Operations *)
(***********************************************************)

(** Initial author: Pierre Crégut, CNET, Lannion, France *)

Module Z.

Include BinNums.IntDef.Z.

Definition t := Z.

(** ** Nicer names [Z.pos] and [Z.neg] for constructors *)

Notation pos := Zpos.
Notation neg := Zneg.

(** ** Constants *)

Definition zero := 0.
Definition one := 1.
Definition two := 2.

(** ** Successor *)

Definition succ x := x + 1.

(** ** Predecessor *)

Definition pred x := x + neg 1.

(** ** Square *)

Definition square x :=
  match x with
    | 0 => 0
    | pos p => pos (Pos.square p)
    | neg p => pos (Pos.square p)
  end.

(** ** Sign function *)

Definition sgn z :=
  match z with
    | 0 => 0
    | pos p => 1
    | neg p => neg 1
  end.

(** Boolean equality and comparisons *)

(** Nota: [geb] and [gtb] are provided for compatibility,
  but [leb] and [ltb] should rather be used instead, since
  more results will be available on them. *)

Definition geb x y :=
  match x ?= y with
    | Lt => false
    | _ => true
  end.

Definition gtb x y :=
  match x ?= y with
    | Gt => true
    | _ => false
  end.

Infix "=?" := eqb (at level 70, no associativity) : Z_scope.
Infix "<=?" := leb (at level 70, no associativity) : Z_scope.
Infix "<?" := ltb (at level 70, no associativity) : Z_scope.
Infix ">=?" := geb (at level 70, no associativity) : Z_scope.
Infix ">?" := gtb (at level 70, no associativity) : Z_scope.

(** ** Absolute value *)

Definition abs z :=
  match z with
    | 0 => 0
    | pos p => pos p
    | neg p => pos p
  end.

(** ** Conversions *)

(** From [Z] to [nat] via absolute value *)

Definition abs_nat (z:Z) : nat :=
  match z with
    | 0 => 0%nat
    | pos p => Pos.to_nat p
    | neg p => Pos.to_nat p
  end.

(** From [Z] to [N] via absolute value *)

Definition abs_N (z:Z) : N :=
  match z with
    | 0 => 0%N
    | pos p => N.pos p
    | neg p => N.pos p
  end.

(** From [Z] to [N] by rounding negative numbers to 0 *)

Definition to_N (z:Z) : N :=
  match z with
    | pos p => N.pos p
    | _ => 0%N
  end.

(** Conversion with a decimal representation for printing/parsing *)

Definition of_uint (d:Decimal.uint) := of_N (Pos.of_uint d).

Definition of_hex_uint (d:Hexadecimal.uint) := of_N (Pos.of_hex_uint d).

Definition of_num_uint (d:Number.uint) :=
  match d with
  | Number.UIntDecimal d => of_uint d
  | Number.UIntHexadecimal d => of_hex_uint d
  end.

Definition of_int (d:Decimal.int) :=
  match d with
  | Decimal.Pos d => of_uint d
  | Decimal.Neg d => opp (of_uint d)
  end.

Definition of_hex_int (d:Hexadecimal.int) :=
  match d with
  | Hexadecimal.Pos d => of_hex_uint d
  | Hexadecimal.Neg d => opp (of_hex_uint d)
  end.

Definition of_num_int (d:Number.int) :=
  match d with
  | Number.IntDecimal d => of_int d
  | Number.IntHexadecimal d => of_hex_int d
  end.

Definition to_int n :=
  match n with
  | 0 => Decimal.Pos Decimal.zero
  | pos p => Decimal.Pos (Pos.to_uint p)
  | neg p => Decimal.Neg (Pos.to_uint p)
  end.

Definition to_hex_int n :=
  match n with
  | 0 => Hexadecimal.Pos Hexadecimal.zero
  | pos p => Hexadecimal.Pos (Pos.to_hex_uint p)
  | neg p => Hexadecimal.Neg (Pos.to_hex_uint p)
  end.

Definition to_num_int n := Number.IntDecimal (to_int n).

Definition to_num_hex_int n := Number.IntHexadecimal (to_hex_int n).

(** ** Iteration of a function

    By convention, iterating a negative number of times is identity.
*)

Definition iter (n:Z) {A} (f:A -> A) (x:A) :=
  match n with
    | pos p => Pos.iter f x p
    | _ => x
  end.

Infix "/" := div : Z_scope.
Infix "mod" := modulo (at level 40, no associativity) : Z_scope.

(** ** Parity functions *)

Definition odd z :=
  match z with
    | 0 => false
    | pos (xO _) => false
    | neg (xO _) => false
    | _ => true
  end.


(** ** Division by two *)

(** [quot2] performs rounding toward zero, it is hence a particular
   case of [quot], and for all relative number [n] we have:
   [n = 2 * quot2 n + if odd n then sgn n else 0].  *)

Definition quot2 (z:Z) :=
  match z with
    | 0 => 0
    | pos 1 => 0
    | pos p => pos (Pos.div2 p)
    | neg 1 => 0
    | neg p => neg (Pos.div2 p)
  end.

(** NB: [Z.quot2] used to be named [Z.div2] in Coq <= 8.3 *)


(** * Base-2 logarithm *)

Definition log2 z :=
  match z with
    | pos (p~1) => pos (Pos.size p)
    | pos (p~0) => pos (Pos.size p)
    | _ => 0
  end.


(** ** Square root *)

Definition sqrt n :=
 match n with
  | pos p => pos (Pos.sqrt p)
  | _ => 0
 end.


(** ** Greatest Common Divisor *)

Definition gcd a b :=
  match a,b with
    | 0, _ => abs b
    | _, 0 => abs a
    | pos a, pos b => pos (Pos.gcd a b)
    | pos a, neg b => pos (Pos.gcd a b)
    | neg a, pos b => pos (Pos.gcd a b)
    | neg a, neg b => pos (Pos.gcd a b)
  end.

(** A generalized gcd, also computing division of a and b by gcd. *)

Definition ggcd a b : Z*(Z*Z) :=
  match a,b with
    | 0, _ => (abs b,(0, sgn b))
    | _, 0 => (abs a,(sgn a, 0))
    | pos a, pos b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (pos aa, pos bb))
    | pos a, neg b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (pos aa, neg bb))
    | neg a, pos b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (neg aa, pos bb))
    | neg a, neg b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (neg aa, neg bb))
  end.


(** ** Bitwise functions *)

(** When accessing the bits of negative numbers, all functions
  below will use the two's complement representation. For instance,
  [-1] will correspond to an infinite stream of true bits. If this
  isn't what you're looking for, you can use [abs] first and then
  access the bits of the absolute value.
*)

(** [testbit] : accessing the [n]-th bit of a number [a].
    For negative [n], we arbitrarily answer [false]. *)

Definition testbit a n :=
 match n with
   | 0 => odd a
   | pos p =>
     match a with
       | 0 => false
       | pos a => Pos.testbit a (N.pos p)
       | neg a => negb (N.testbit (Pos.pred_N a) (N.pos p))
     end
   | neg _ => false
 end.

(** Bitwise operations [lor] [land] [ldiff] [lxor] *)

Definition ldiff a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => a
   | pos a, pos b => of_N (Pos.ldiff a b)
   | neg a, pos b => neg (N.succ_pos (N.lor (Pos.pred_N a) (N.pos b)))
   | pos a, neg b => of_N (N.land (N.pos a) (Pos.pred_N b))
   | neg a, neg b => of_N (N.ldiff (Pos.pred_N b) (Pos.pred_N a))
 end.

Number Notation Z of_num_int to_num_hex_int : hex_Z_scope.
Number Notation Z of_num_int to_num_int : Z_scope.

End Z.

(** Re-export the notation for those who just [Import BinIntDef] *)
Number Notation Z Z.of_num_int Z.to_num_hex_int : hex_Z_scope.
Number Notation Z Z.of_num_int Z.to_num_int : Z_scope.
