
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import BigNumPrelude.
Require Export Int31Native.

Set Vm Optimize.


Local Open Scope int31_scope.
Local Open Scope bool_scope.

(** The number of digits as a int31 *)
Definition digits := 31.

(** The bigger int *)
Definition max_int31 := Eval compute in 0 - 1.
Register max_int31 as Inline.

(** Access to the nth digits *)
Definition get_digit x p := (0 < (x land (1 << p))).

Definition set_digit x p (b:bool) :=
  if (0 <= p) && (p < 31) then 
    if b then x lor (1 << p)
    else x land (max_int31 lxor (1 << p))
  else x.

(** Equality to 0 *)
Definition is_zero (i:int31) := i == 0.
Register is_zero as Inline.

(** Parity *)
Definition is_even (i:int31) := is_zero (i land 1).
Register is_even as Inline.

(** Extra modulo operations *)
Definition opp31 (i:int31) := 0 - i.
Register opp31 as Inline.
Notation "- x" := (opp31 x) : int31_scope.

Definition opp31carry i := max_int31 - i.
Register is_zero as Inline.

Definition succ31 i := i + 1.
Register opp31carry as Inline.

Definition pred31 i := i - 1.
Register pred31 as Inline.

Definition add31carry i j := i + j + 1.
Register add31carry as Inline.

Definition sub31carry i j := i - j - 1.
Register sub31carry as Inline.

(** Exact arithmetic operations *)

Definition add31c_def x y :=
  let r := x + y in
  if r < x then C1 r else C0 r.
(* the same but direct implementation for effeciancy *)
Register add31c      : int31 -> int31 -> carry int31 as int31_addc.
Notation "n '+c' m" := (add31c n m) (at level 50, no associativity) : int31_scope.

Definition add31carryc_def x y :=
  let r := add31carry x y in
  if r <= x then C1 r else C0 r.
(* the same but direct implementation for effeciancy *)
Register add31carryc : int31 -> int31 -> carry int31 as int31_addcarryc.

Definition sub31c_def x y := 
  if y <= x then C0 (x - y) else C1 (x - y).
(* the same but direct implementation for effeciancy *)
Register sub31c      : int31 -> int31 -> carry int31 as int31_subc.
Notation "n '-c' m" := (sub31c n m) (at level 50, no associativity) : int31_scope.

Definition sub31carryc_def x y :=
  if y < x then C0 (x - y - 1) else C1 (x - y - 1).
(* the same but direct implementation for effeciancy *)
Register sub31carryc : int31 -> int31 -> carry int31 as int31_subcarryc.

Definition diveucl31_def x y := (x/y, x\%y).
(* the same but direct implementation for effeciancy *) 
Register diveucl31   : int31 -> int31 -> int31 * int31 as int31_diveucl.

Register diveucl31_21    : int31 -> int31 -> int31 -> int31 * int31 as int31_div21.

Definition addmuldiv31_def p x y :=
  (x << p) lor (y >> (digits - p)).
Register addmuldiv31   : int31 -> int31 -> int31 -> int31 as int31_addmuldiv.

Definition opp31c (i:int31) := 0 -c i.
Register opp31c as Inline.

Definition succ31c i := i +c 1.
Register succ31c as Inline.

Definition pred31c i := i -c 1.
Register pred31c as Inline.

(** Comparison *)
Definition compare31_def x y :=
  if x < y then Lt 
  else if (x == y) then Eq else Gt.

Register compare31 : int31 -> int31 -> comparison as int31_compare.
Notation "n ?= m" := (compare31 n m) (at level 70, no associativity) : int31_scope.

(** Exotic operations *)

Register head0 : int31 -> int31 as int31_head0.
Register tail0 : int31 -> int31 as int31_tail0.

(** Iterators *)

Definition foldi A (f:int31 -> A -> A) from to :=
  foldi_cont31 A A (fun i cont a => cont (f i a)) from to (fun a => a).
Register foldi as Inline.

Definition fold A (f: A -> A) from to :=
  foldi_cont31 A A (fun i cont a => cont (f a)) from to (fun a => a).
Register fold as Inline.

Definition foldi_down A (f:int31 -> A -> A) from downto :=
  foldi_down_cont31 A A (fun i cont a => cont (f i a)) from downto (fun a => a).
Register foldi_down as Inline.

Definition fold_down A (f:A -> A) from downto :=
  foldi_down_cont31 A A (fun i cont a => cont (f a)) from downto (fun a => a).
Register fold_down as Inline.

Definition forallb (f:int31 -> bool) from to :=
  foldi_cont31 _ bool (fun i cont _ => if f i then cont tt else false) from to (fun _ => true) tt.

Definition existsb (f:int31 -> bool) from to :=
  foldi_cont31 _ bool (fun i cont _ => if f i then true else cont tt) from to (fun _ => false) tt.

(** Translation to Z *)
Fixpoint to_Z_rec (n:nat) (i:int31) :=
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
Fixpoint gcd31_rec (guard:nat) (i j:int31) {struct guard} :=
   match guard with
   | O => 1
   | S p => if j == 1 then i else gcd31_rec p j (i \% j)
   end.

Definition gcd31 := gcd31_rec (2*size).

(** Square root functions using newton iteration **)

Definition sqrt31_step (rec: int31 -> int31 -> int31) (i j: int31)  :=
  let quo := i/j in
  if quo < j then rec i ((j + i/j) >> 1)
  else j.

Definition iter31_sqrt :=
 Eval lazy beta delta [sqrt31_step] in
 fix iter31_sqrt (n: nat) (rec: int31 -> int31 -> int31)
          (i j: int31) {struct n} : int31 :=
  sqrt31_step
   (fun i j => match n with
      O =>  rec i j
   | S n => (iter31_sqrt n (iter31_sqrt n rec)) i j
   end) i j.

Definition sqrt31 i :=
  match compare31 1 i with
    Gt => 0
  | Eq => 1
  | Lt => iter31_sqrt 31 (fun i j => j) i (i >> 1)
  end.

Definition sqrt312_step (rec: int31 -> int31 -> int31 -> int31)
   (ih il j: int31)  :=
  if ih < j then
    let (quo,_) := diveucl31_21 ih il j in
    if quo < j then
      let m := 
        match j +c quo with
        | C0 m1 => m1 >> 1
        | C1 m1 => (m1 >> 1) + 30
        end in 
      rec ih il m
    else j
  else j.

Definition iter312_sqrt :=
 Eval lazy beta delta [sqrt312_step] in
 fix iter312_sqrt (n: nat)
          (rec: int31  -> int31 -> int31 -> int31)
          (ih il j: int31) {struct n} : int31 :=
  sqrt312_step
   (fun ih il j => 
     match n with
     | O =>  rec ih il j
     | S n => (iter312_sqrt n (iter312_sqrt n rec)) ih il j
   end) ih il j.

Definition sqrt312 ih il :=
  let s := iter312_sqrt 31 (fun ih il j => j) ih il max_int31 in
  let (ih1, il1) := mul31c s s in
  match il -c il1 with
  | C0 il2 =>
    if ih1 < ih then (s, C1 il2) else (s, C0 il2)
  | C1 il2 =>
    if ih1 < (ih - 1) then (s, C1 il2) else (s, C0 il2)
  end.


(*
Require Import Int31Bool.
Print to_Z.
Check get_digit.
Print Int31_to_Z.

Fixpoint to_Z2_aux (n:nat) (x:int31) z := 
 match n with
 | O => z
 | S n' =>
   to_Z2_aux n' x (Zdigit_of_bool (get_digit x (of_Z (Z_of_nat n'))) z)
 end.

Definition to_Z2 x := to_Z2_aux size x Z0.

Require Import Bvector.
Print Module Bvector.
Print Bvector.
Fixpoint to_bvect (n:nat) (x:int31) : Bvector n :=
 match n as n0 return Bvector n0 with
 | O => Bnil
 | S n' => Bcons (get_digit x (of_Z (Z_of_nat n'))) n' (to_bvect n' x)
 end.
Print Blow.
Print Bhigh.

Check set_digit.

Fixpoint of_bvect (n:nat) : Bvector n -> int31 :=
 match n as n0 return Bvector n0 -> int31 with
 | O => fun _ => 0
 | S n' => fun v => set_digit (of_bvect n' (Bhigh n' v)) (of_Z (Z_of_nat n')) (Blow n' v)
 end.

Axiom get_set_same : forall x p b,
  ( (0 <= p) && (p < digits))%bool = true ->
  get_digit (set_digit x p b) p = b.

Axiom get_set_diff : forall x p p1 b1,
  (p == p1)%bool = false ->
  get_digit (set_digit x p1 b1) p = get_digit x p.

Lemma toto : forall n v, to_bvect n (of_bvect n v) = v.
Proof.
 induction n;simpl;intros.
 intros;symmetry;apply V0_eq.
SearchAbout Vcons.
 rewrite (VSn_eq _ _ v);simpl.
 rewrite get_set_same.
 unfold Bcons.
 apply f_equal.
Lemma tutu : forall n n' x b, (n <= n')%nat -> to_bvect n (set_digit x (of_Z (Z_of_nat n')) b) = to_bvect n x.
Proof.
 induction n;simpl;intros;trivial.
 rewrite get_set_diff.
 apply f_equal.
 apply IHn;auto with arith.
 


 SearchAbout Vhead.
Print Blow.
 SearchAbout Vlow.
SearchAbout Blow.



Print Module Bvector.
Check vec.

Fixpoint mult_pow2 n z :=
 match n with
 | O => z
 | S n => Zdouble (mult_pow2 n z)
 end.

Axiom lsl_spec : forall x p, to_Z2 (x << p) = (to_Z2 x * 2 ^ to_Z2 p) mod (2 ^ Z_of_nat size).

Fixpoint Plor p1 p2 :=
 match p1, p2 with
 | xH, xH => 1%Z
 | xH, xO p2=> Zdouble_plus_one (Zpos p2)
 | xH, xI p2 => Zdouble_plus_one (Zpos p2)
 | xO p1, xH => Zdouble_plus_one (Zpos p1)
 | xI p2, xH => Zdouble_plus_one (Zpos p1)
 | xO p1, xO p2 => Zdouble (Plor p1 p2)
 | xI p1, xO p2 => Zdouble_plus_one (Plor p1 p2)
 | xO p1, xI p2 => Zdouble_plus_one (Plor p1 p2)
 | xI p1, xI p2 => Zdouble_plus_one (Plor p1 p2)
 end.

Definition Zlor z1 z2 :=
 match z1, z2 with
 | Z0, _ => z2
 | _, Z0 => z1
 | Zpos p1, Zpos p2 => Zpos (Plor p1 p2)
 | Zneg p1, Zpos p2 => Zneg (Plor p1 p2)
 | Zpos p1, Zneg p2 => Zneg (Plor p1 p2)
 | Zneg p1, Zneg p2 => Zneg (Plor p1 p2)
 end.

Axiom lor_spec : forall x y, to_Z2 (x lor y) = Zlor (to_Z2 x) (to_Z2 y).

Lemma toto : forall x, to_Z2 ((x << 1) lor 1) = (2*to_Z2 x+1) mod (2 ^ Z_of_nat size).
Proof.
 intros;rewrite lor_spec.
 rewrite lsl_spec.
 set (y:= to_Z2 1);change y with 1%Z;clear y.
 change (2 ^ 1)%Z with 2%Z.
 rewrite Zmult_comm.
Lemma tutu : forall z, Zlor (2*z) 1 = (2*z + 1)%Z.
Proof.
 destruct z;simpl.


Lemma toto : forall x, to_Z2 size x = 1.
intros.
 unfold to_Z2;simpl.
*)
