(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Notations Logic Datatypes.
Require Decimal.
Local Open Scope nat_scope.

(**********************************************************************)
(** * Peano natural numbers, definitions of operations *)
(**********************************************************************)

(** This file is meant to be used as a whole module,
    without importing it, leading to qualified definitions
    (e.g. Nat.pred) *)

Definition t := nat.

(** ** Constants *)

Local Notation "0" := O.
Local Notation "1" := (S O).
Local Notation "2" := (S (S O)).

Definition zero := 0.
Definition one := 1.
Definition two := 2.

(** ** Basic operations *)

Definition succ := S.

Definition pred n :=
  match n with
    | 0 => n
    | S u => u
  end.

Fixpoint add n m :=
  match n with
  | 0 => m
  | S p => S (p + m)
  end

where "n + m" := (add n m) : nat_scope.

Definition double n := n + n.

Fixpoint mul n m :=
  match n with
  | 0 => 0
  | S p => m + p * m
  end

where "n * m" := (mul n m) : nat_scope.

(** Truncated subtraction: [n-m] is [0] if [n<=m] *)

Fixpoint sub n m :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end

where "n - m" := (sub n m) : nat_scope.

(** ** Comparisons *)

Fixpoint eqb n m : bool :=
  match n, m with
    | 0, 0 => true
    | 0, S _ => false
    | S _, 0 => false
    | S n', S m' => eqb n' m'
  end.

Fixpoint leb n m : bool :=
  match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
  end.

Definition ltb n m := leb (S n) m.

Infix "=?" := eqb (at level 70) : nat_scope.
Infix "<=?" := leb (at level 70) : nat_scope.
Infix "<?" := ltb (at level 70) : nat_scope.

Fixpoint compare n m : comparison :=
  match n, m with
   | 0, 0 => Eq
   | 0, S _ => Lt
   | S _, 0 => Gt
   | S n', S m' => compare n' m'
  end.

Infix "?=" := compare (at level 70) : nat_scope.

(** ** Minimum, maximum *)

Fixpoint max n m :=
  match n, m with
    | 0, _ => m
    | S n', 0 => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m :=
  match n, m with
    | 0, _ => 0
    | S n', 0 => 0
    | S n', S m' => S (min n' m')
  end.

(** ** Parity tests *)

Fixpoint even n : bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
  end.

Definition odd n := negb (even n).

(** ** Power *)

Fixpoint pow n m :=
  match m with
    | 0 => 1
    | S m => n * (n^m)
  end

where "n ^ m" := (pow n m) : nat_scope.

(** ** Tail-recursive versions of [add] and [mul] *)

Fixpoint tail_add n m :=
  match n with
    | O => m
    | S n => tail_add n (S m)
  end.

(** [tail_addmul r n m] is [r + n * m]. *)

Fixpoint tail_addmul r n m :=
  match n with
    | O => r
    | S n => tail_addmul (tail_add m r) n m
  end.

Definition tail_mul n m := tail_addmul 0 n m.

(** ** Conversion with a decimal representation for printing/parsing *)

Local Notation ten := (S (S (S (S (S (S (S (S (S (S O)))))))))).

Fixpoint of_uint_acc (d:Decimal.uint)(acc:nat) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 d => of_uint_acc d (tail_mul ten acc)
  | Decimal.D1 d => of_uint_acc d (S (tail_mul ten acc))
  | Decimal.D2 d => of_uint_acc d (S (S (tail_mul ten acc)))
  | Decimal.D3 d => of_uint_acc d (S (S (S (tail_mul ten acc))))
  | Decimal.D4 d => of_uint_acc d (S (S (S (S (tail_mul ten acc)))))
  | Decimal.D5 d => of_uint_acc d (S (S (S (S (S (tail_mul ten acc))))))
  | Decimal.D6 d => of_uint_acc d (S (S (S (S (S (S (tail_mul ten acc)))))))
  | Decimal.D7 d => of_uint_acc d (S (S (S (S (S (S (S (tail_mul ten acc))))))))
  | Decimal.D8 d => of_uint_acc d (S (S (S (S (S (S (S (S (tail_mul ten acc)))))))))
  | Decimal.D9 d => of_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul ten acc))))))))))
  end.

Definition of_uint (d:Decimal.uint) := of_uint_acc d O.

Fixpoint to_little_uint n acc :=
  match n with
  | O => acc
  | S n => to_little_uint n (Decimal.Little.succ acc)
  end.

Definition to_uint n :=
  Decimal.rev (to_little_uint n Decimal.zero).

Definition of_int (d:Decimal.int) : option nat :=
  match Decimal.norm d with
    | Decimal.Pos u => Some (of_uint u)
    | _ => None
  end.

Definition to_int n := Decimal.Pos (to_uint n).

(** ** Euclidean division *)

(** This division is linear and tail-recursive.
    In [divmod], [y] is the predecessor of the actual divisor,
    and [u] is [y] minus the real remainder
*)

Fixpoint divmod x y q u :=
  match x with
    | 0 => (q,u)
    | S x' => match u with
                | 0 => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.

Definition div x y :=
  match y with
    | 0 => y
    | S y' => fst (divmod x y' 0 y')
  end.

Definition modulo x y :=
  match y with
    | 0 => y
    | S y' => y' - snd (divmod x y' 0 y')
  end.

Infix "/" := div : nat_scope.
Infix "mod" := modulo (at level 40, no associativity) : nat_scope.


(** ** Greatest common divisor *)

(** We use Euclid algorithm, which is normally not structural,
    but Coq is now clever enough to accept this (behind modulo
    there is a subtraction, which now preserves being a subterm)
*)

Fixpoint gcd a b :=
  match a with
   | O => b
   | S a' => gcd (b mod (S a')) (S a')
  end.

(** ** Square *)

Definition square n := n * n.

(** ** Square root *)

(** The following square root function is linear (and tail-recursive).
  With Peano representation, we can't do better. For faster algorithm,
  see Psqrt/Zsqrt/Nsqrt...

  We search the square root of n = k + p^2 + (q - r)
  with q = 2p and 0<=r<=q. We start with p=q=r=0, hence
  looking for the square root of n = k. Then we progressively
  decrease k and r. When k = S k' and r=0, it means we can use (S p)
  as new sqrt candidate, since (S k')+p^2+2p = k'+(S p)^2.
  When k reaches 0, we have found the biggest p^2 square contained
  in n, hence the square root of n is p.
*)

Fixpoint sqrt_iter k p q r :=
  match k with
    | O => p
    | S k' => match r with
                | O => sqrt_iter k' (S p) (S (S q)) (S (S q))
                | S r' => sqrt_iter k' p q r'
              end
  end.

Definition sqrt n := sqrt_iter n 0 0 0.

(** ** Log2 *)

(** This base-2 logarithm is linear and tail-recursive.

  In [log2_iter], we maintain the logarithm [p] of the counter [q],
  while [r] is the distance between [q] and the next power of 2,
  more precisely [q + S r = 2^(S p)] and [r<2^p]. At each
  recursive call, [q] goes up while [r] goes down. When [r]
  is 0, we know that [q] has almost reached a power of 2,
  and we increase [p] at the next call, while resetting [r]
  to [q].

  Graphically (numbers are [q], stars are [r]) :

<<
                    10
                  9
                8
              7   *
            6       *
          5           ...
        4
      3   *
    2       *
  1   *       *
0   *   *       *
>>

  We stop when [k], the global downward counter reaches 0.
  At that moment, [q] is the number we're considering (since
  [k+q] is invariant), and [p] its logarithm.
*)

Fixpoint log2_iter k p q r :=
  match k with
    | O => p
    | S k' => match r with
                | O => log2_iter k' (S p) (S q) q
                | S r' => log2_iter k' p (S q) r'
              end
  end.

Definition log2 n := log2_iter (pred n) 0 1 0.

(** Iterator on natural numbers *)

Definition iter (n:nat) {A} (f:A->A) (x:A) : A :=
 nat_rect (fun _ => A) x (fun _ => f) n.

(** Bitwise operations *)

(** We provide here some bitwise operations for unary numbers.
  Some might be really naive, they are just there for fullfiling
  the same interface as other for natural representations. As
  soon as binary representations such as NArith are available,
  it is clearly better to convert to/from them and use their ops.
*)

Fixpoint div2 n :=
  match n with
  | 0 => 0
  | S 0 => 0
  | S (S n') => S (div2 n')
  end.

Fixpoint testbit a n : bool :=
 match n with
   | 0 => odd a
   | S n => testbit (div2 a) n
 end.

Definition shiftl a := nat_rect _ a (fun _ => double).
Definition shiftr a := nat_rect _ a (fun _ => div2).

Fixpoint bitwise (op:bool->bool->bool) n a b :=
 match n with
  | 0 => 0
  | S n' =>
    (if op (odd a) (odd b) then 1 else 0) +
    2*(bitwise op n' (div2 a) (div2 b))
 end.

Definition land a b := bitwise andb a a b.
Definition lor a b := bitwise orb (max a b) a b.
Definition ldiff a b := bitwise (fun b b' => andb b (negb b')) a a b.
Definition lxor a b := bitwise xorb (max a b) a b.
