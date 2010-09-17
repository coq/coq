
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)
Require Export Int31Native.
Require Import BigNumPrelude.
Require Import Bvector.

Set Vm Optimize.


Local Open Scope int31_scope.

(** The number of digits as a int *)
Definition digits := 31.

(** The bigger int *)
Definition max_int := Eval compute in 0 - 1.
Register max_int as Inline.

(** Access to the nth digits *)
Definition get_digit x p := (0 < (x land (1 << p))).

Definition set_digit x p (b:bool) :=
  if (0 <= p) && (p < digits) then 
    if b then x lor (1 << p)
    else x land (max_int lxor (1 << p))
  else x.

(** Equality to 0 *)
Definition is_zero (i:int) := i == 0.
Register is_zero as Inline.

(** Parity *)
Definition is_even (i:int) := is_zero (i land 1).
Register is_even as Inline.

(** Bit *)

Definition bit i n :=  negb (is_zero ((i >> n) << (digits - 1))).
Register bit as Inline.

(** Extra modulo operations *)
Definition opp (i:int) := 0 - i.
Register opp as Inline.
Notation "- x" := (opp x) : int31_scope.

Definition oppcarry i := max_int - i.
Register oppcarry as Inline.

Definition succ i := i + 1.
Register succ as Inline.

Definition pred i := i - 1.
Register pred as Inline.

Definition addcarry i j := i + j + 1.
Register addcarry as Inline.

Definition subcarry i j := i - j - 1.
Register subcarry as Inline.

(** Exact arithmetic operations *)

Definition addc_def x y :=
  let r := x + y in
  if r < x then C1 r else C0 r.
(* the same but direct implementation for effeciancy *)
Register addc      : int -> int -> carry int as int31_addc.
Notation "n '+c' m" := (addc n m) (at level 50, no associativity) : int31_scope.

Definition addcarryc_def x y :=
  let r := addcarry x y in
  if r <= x then C1 r else C0 r.
(* the same but direct implementation for effeciancy *)
Register addcarryc : int -> int -> carry int as int31_addcarryc.

Definition subc_def x y := 
  if y <= x then C0 (x - y) else C1 (x - y).
(* the same but direct implementation for effeciancy *)
Register subc      : int -> int -> carry int as int31_subc.
Notation "n '-c' m" := (subc n m) (at level 50, no associativity) : int31_scope.

Definition subcarryc_def x y :=
  if y < x then C0 (x - y - 1) else C1 (x - y - 1).
(* the same but direct implementation for effeciancy *)
Register subcarryc : int -> int -> carry int as int31_subcarryc.

Definition diveucl_def x y := (x/y, x\%y).
(* the same but direct implementation for effeciancy *) 
Register diveucl   : int -> int -> int * int as int31_diveucl.

Register diveucl_21    : int -> int -> int -> int * int as int31_div21.

Definition addmuldiv_def p x y :=
  (x << p) lor (y >> (digits - p)).
Register addmuldiv   : int -> int -> int -> int as int31_addmuldiv.

Definition oppc (i:int) := 0 -c i.
Register oppc as Inline.

Definition succc i := i +c 1.
Register succc as Inline.

Definition predc i := i -c 1.
Register predc as Inline.

(** Comparison *)
Definition compare_def x y :=
  if x < y then Lt 
  else if (x == y) then Eq else Gt.

Register compare : int -> int -> comparison as int31_compare.
Notation "n ?= m" := (compare n m) (at level 70, no associativity) : int31_scope.

(** Exotic operations *)

(** I should add the definition (like for compare) *)
Register head0 : int -> int as int31_head0.
Register tail0 : int -> int as int31_tail0.

(** Iterators *)

Definition foldi {A} (f:int -> A -> A) from to :=
  foldi_cont (fun i cont a => cont (f i a)) from to (fun a => a).
Register foldi as Inline.

Definition fold {A} (f: A -> A) from to :=
  foldi_cont (fun i cont a => cont (f a)) from to (fun a => a).
Register fold as Inline.

Definition foldi_down {A} (f:int -> A -> A) from downto :=
  foldi_down_cont (fun i cont a => cont (f i a)) from downto (fun a => a).
Register foldi_down as Inline.

Definition fold_down {A} (f:A -> A) from downto :=
  foldi_down_cont (fun i cont a => cont (f a)) from downto (fun a => a).
Register fold_down as Inline.

Definition forallb (f:int -> bool) from to :=
  foldi_cont (fun i cont _ => if f i then cont tt else false) from to (fun _ => true) tt.

Definition existsb (f:int -> bool) from to :=
  foldi_cont (fun i cont _ => if f i then true else cont tt) from to (fun _ => false) tt.

(** Translation to Z *)

Fixpoint to_Z_rec (n:nat) (i:int) :=
  match n with 
  | O => 0%Z 
  | S n => 
    (if is_even i then Zdouble else Zdouble_plus_one) (to_Z_rec n (i >> 1))
  end.

Definition to_Z := to_Z_rec size.

Fixpoint of_pos_rec (n:nat) (p:positive) :=
  match n, p with 
  | O, _ => 0
  | S n, xH => 1
  | S n, xO p => (of_pos_rec n p) << 1
  | S n, xI p => (of_pos_rec n p) << 1 lor 1
  end.

Definition of_pos := of_pos_rec size.

Definition of_Z z := 
  match z with
  | Zpos p => of_pos p
  | Z0 => 0
  | Zneg p => - (of_pos p)
  end.

(** Gcd **)
Fixpoint gcd_rec (guard:nat) (i j:int) {struct guard} :=
   match guard with
   | O => 1
   | S p => if j == 0 then i else gcd_rec p j (i \% j)
   end.

Definition gcd := gcd_rec (2*size).

(** Square root functions using newton iteration **)

Definition sqrt_step (rec: int -> int -> int) (i j: int)  :=
  let quo := i/j in
  if quo < j then rec i ((j + i/j) >> 1)
  else j.

Definition iter_sqrt :=
 Eval lazy beta delta [sqrt_step] in
 fix iter_sqrt (n: nat) (rec: int -> int -> int)
          (i j: int) {struct n} : int :=
  sqrt_step
   (fun i j => match n with
      O =>  rec i j
   | S n => (iter_sqrt n (iter_sqrt n rec)) i j
   end) i j.

Definition sqrt i :=
  match compare 1 i with
    Gt => 0
  | Eq => 1
  | Lt => iter_sqrt size (fun i j => j) i (i >> 1)
  end.

Definition sqrt2_step (rec: int -> int -> int -> int)
   (ih il j: int)  :=
  if ih < j then
    let (quo,_) := diveucl_21 ih il j in
    if quo < j then
      match j +c quo with
      | C0 m1 => rec ih il (m1 >> 1)
      | C1 m1 => rec ih il ((m1 >> 1) + 30)
      end 
    else j
  else j.

Definition iter2_sqrt :=
 Eval lazy beta delta [sqrt2_step] in
 fix iter2_sqrt (n: nat)
          (rec: int  -> int -> int -> int)
          (ih il j: int) {struct n} : int :=
  sqrt2_step
   (fun ih il j => 
     match n with
     | O =>  rec ih il j
     | S n => (iter2_sqrt n (iter2_sqrt n rec)) ih il j
   end) ih il j.

Definition sqrt2 ih il :=
  let s := iter2_sqrt size (fun ih il j => j) ih il max_int in
  let (ih1, il1) := mulc s s in
  match il -c il1 with
  | C0 il2 =>
    if ih1 < ih then (s, C1 il2) else (s, C0 il2)
  | C1 il2 =>
    if ih1 < (ih - 1) then (s, C1 il2) else (s, C0 il2)
  end.
