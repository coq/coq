
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)
Require Import List.
Require Import NaryFunctions.
Require Export BigNumPrelude.
Require Export Int31Native.
Require Export Int31Op.
Require Export Int31Bool.

(* Bijection : int31 <-> Int31 *)

Definition to_Int31 x :=
  Eval cbv beta iota zeta delta [nuncurry size nprod_of_list foldi foldi_cont31 sub31 digits]  in 
    (nuncurry _ _ size I31 (nprod_of_list _ (foldi _  (fun i l => get_digit x i :: l) 0 (digits - 1)%int31 nil))).

Definition of_Int31 x := 
 Eval lazy beta iota delta [nfold size sub31] in
 snd (Int31_rect (fun _ => (int31 * int31)%type)
   (nfold _ _ (fun b (res:int31 * int31) =>
                let (pos, i) := res in
                ((pos-1)%int31, set_digit i pos b)) (30,0)%int31 size) x).

Axiom get_set_same : forall x p b,
  ( (0 <= p) && (p < digits))%bool = true ->
  get_digit (set_digit x p b) p = b.

Axiom get_set_diff : forall x p p1 b1,
  (p == p1)%bool = false ->
  get_digit (set_digit x p1 b1) p = get_digit x p.

Axiom to_Int31_inj : forall x y, to_Int31 x = to_Int31 y -> x = y.


(** Specification of logical operations *)

Axiom lsl_spec : forall x p, to_Int31 (x << p) = nshiftl (Zabs_nat (to_Z p)) (to_Int31 x).

Axiom lsr_spec : forall x p, to_Int31 (x >> p) = nshiftr (Zabs_nat (to_Z p)) (to_Int31 x).

Axiom lor_spec : forall x y, (x lor y)%int31 = of_Int31 (Ilor (to_Int31 x) (to_Int31 y)).

Axiom land_spec : forall x y, (x land y)%int31 = of_Int31 (Iland (to_Int31 x) (to_Int31 y)).

Axiom lxor_spec : forall x y, (x lxor y)%int31 = of_Int31 (Ilxor (to_Int31 x) (to_Int31 y)).

(** Specification of basic opetations *)

(* Arithmetic modulo operations *)

Local Open Scope int31_scope.

Local Notation wB := (2^(Z_of_nat size)).

Local Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99).

Axiom add31_spec : forall x y, of_Z (x + y) = of_Z x + of_Z y.

Axiom sub31_spec : forall x y, of_Z (x - y) = of_Z x - of_Z y.

Axiom mul31_spec : forall x y, of_Z (x * y) = of_Z x * of_Z y.

Axiom mul31c_spec : forall x y, (to_Z x * to_Z y = to_Z (fst (mul31c x y)) * wB + to_Z (snd (mul31c x y)))%Z.

Axiom div31_spec : forall x y, of_Z (x / y) = of_Z x / of_Z y.

Axiom mod31_spec : forall x y, of_Z (x mod y) = of_Z x \% of_Z y.

(* Comparisons *)
Axiom eq31_spec : forall x y, (x == y)%bool = true <-> x = y.

Axiom lt31_spec : forall x y, (x < y)%bool = true <-> to_Z x < to_Z y.

Axiom le31_spec : forall x y, (x <= y)%bool = true <-> to_Z x <= to_Z y.

(** Iterators *)

Axiom foldi_cont31_gt : forall A B f from to cont a,
  (to < from)%bool = true -> foldi_cont31 A B f from to cont a = cont a.

Axiom foldi_cont31_eq : forall A B f from to cont a,
  from = to -> foldi_cont31 A B f from to cont a = f from cont a.

Axiom foldi_cont31_lt : forall A B f from to cont a,
  (from < to)%bool = true-> 
  foldi_cont31 A B f from to cont a = 
  f from (fun a' => foldi_cont31 A B f (from+1) to cont a') a.

Axiom foldi_down_cont31_lt : forall A B f from downto cont a,
  (from < downto)%bool = true -> foldi_down_cont31 A B f from downto cont a = cont a.

Axiom foldi_down_cont31_eq : forall A B f from downto cont a,
  from = downto -> foldi_down_cont31 A B f from downto cont a = f from cont a.

Axiom foldi_down_cont31_gt : forall A B f from downto cont a,
  (downto < from)%bool = true-> 
  foldi_down_cont31 A B f from downto cont a = 
  f from (fun a' => foldi_down_cont31 A B f (from-1) downto cont a') a.

(** Print *)

Axiom print_int_spec : forall x, x = print_int x.

(** Axioms on operations which are just short cut *)

Axiom compare31_spec : forall x y, compare31 x y = compare31_def x y.

Axiom head0_spec  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|head0 x|]) * [|x|] < wB.

Axiom tail0_spec  : forall x, 0 < [|x|] ->
         (exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail0 x|]))%Z.

Axiom add31c_spec : forall x y, x +c y = add31c_def x y.

Axiom add31carryc_spec : forall x y, add31carryc x y = add31carryc_def x y.

Axiom sub31c_spec : forall x y, x -c y = sub31c_def x y.

Axiom sub31carryc : forall x y, sub31carryc x y = sub31carryc_def x y.

Axiom diveucl31_spec : forall x y, diveucl31 x y = diveucl31_def x y.

Axiom diveucl31_21_spec :  forall a1 a2 b,
   let (q,r) := diveucl31_21 a1 a2 b in
   ([|q|],[|r|]) = Zdiv_eucl ([|a1|] * wB + [|a2|]) [|b|].

Axiom addmuldiv31_spec : forall p x y,
  addmuldiv31 p x y = addmuldiv31_def p x y.

(*

SearchAbout Int31_to_Z.

Lemma Zdigit_of_bool b1 z1 = Zdigit_of_bool b2 z2 ->
      b1 = b2 /\ z1 = z2.

Print Int31_to_Z.

Check Int31_to_Z.


Definition nshiftl n := iter_nat n _ shiftl.
Definition nshiftr n := iter_nat n _ shiftr.

Definition addmuldiv n x y :=
  Ilor (nshiftl n x) (nshiftr (31 - n)%nat y).

Lemma toto : forall n x y, addmuldiv (S n) x y = 
    addmuldiv 1 (addmuldiv n x y) (shiftl y).
Proof.
Admitted.

Lemma Zdiv_power2_S : forall x n, (x / 2 ^ Z_of_nat (S n) = (x / 2) / 2 ^ Z_of_nat n)%Z.
Proof.
 intros;rewrite inj_S, Zpower_Zsucc, Zdiv_Zdiv;auto with zarith.
Qed.

Lemma Zdigit_of_bool_mult : forall x b, (x * 2 + Zdigit_of_bool b 0 = Zdigit_of_bool b x)%Z.
Proof.
 intros x;destruct b;simpl.
 rewrite Zdouble_plus_one_mult;ring.
 rewrite Zdouble_mult;ring.
Qed.

Axiom Int31_to_Z_bounded : forall x, (0<= Int31_to_Z x < 2 ^ Z_of_nat size).

Lemma addmuldiv1_spec : forall x y, 
 (Int31_to_Z (addmuldiv 1 x y) = ((Int31_to_Z x * 2 ^ Z_of_nat size + Int31_to_Z y) / 2^(Z_of_nat (size - 1))) mod 2 ^ Z_of_nat size)%Z.
Proof.
 assert (H:forall s, s = size ->
  forall x y, 
   (Int31_to_Z (addmuldiv 1 x y) = 
   ((Int31_to_Z x * 2 ^ Z_of_nat s + Int31_to_Z y) / 2^(Z_of_nat (s - 1))) mod 2 ^ Z_of_nat s)%Z);
 [ | apply H;trivial].
 destruct x;destruct y;simpl.
 repeat rewrite Bool.orb_false_r.
 assert (2 ^ Z_of_nat s = 2 * 2 ^ (Z_of_nat (s - 1)))%Z.
  rewrite H;reflexivity.
 rewrite H0 at 1.
 rewrite Zmult_assoc, Z_div_plus_l.
 rewrite H at 1.
 let s1 := eval compute in (size - 1)%nat in change (size - 1)%nat with s1.
 repeat rewrite Zdiv_power2_S, Zdigit_fo_bool_div2.
 change (2 ^ Z_of_nat 0)%Z with 1%Z.
 rewrite Zdiv_1_r.
 rewrite Zdigit_of_bool_mult;trivial.
 match goal with |- _ = (?x mod _) => pos_Zdigit x end.
 rewrite H;unfold size.
 repeat (rewrite Zdigit_of_bool_mod2;[ | trivial]).
 replace (Zdigit_of_bool b 0 mod 2 ^ Z_of_nat 0)%Z with 0%Z;trivial.
 simpl;rewrite Zmod_1_r;trivial.
 rewrite H;reflexivity.
Qed.

Parameter set_digit : int31 -> int31 -> bool -> int31.

Axiom get_set_same : forall x p b,
  ( (0 <= p) && (p < digits))%bool = true ->
  digit (set_digit x p b) p = b.

Axiom get_set_diff : forall x p p1 b1,
  (p == p1) = false ->
  digit (set_digit x p1 b1) p = digit x p.

Lemma get_set2_diff : forall x p p1 p2 b1 b2,
  (p == p1) = false ->
  (p == p2) = false ->
  digit (set_digit (set_digit x p1 b1) p2 b2) p = digit x p.
Proof.
 intros;repeat (rewrite get_set_diff;trivial).
Qed.

Lemma get_set4_diff : forall x p p1 p2 p3 p4 b1 b2 b3 b4,
  (p == p1) = false ->
  (p == p2) = false ->
  (p == p3) = false ->
  (p == p4) = false ->
  digit (set_digit (set_digit (set_digit (set_digit x p1 b1) p2 b2) p3 b3) p4 b4) p = digit x p.
Proof.
 intros;repeat (rewrite get_set_diff;trivial).
Qed.


Lemma get_set8_diff : forall x p p1 p2 p3 p4 p5 p6 p7 p8 b1 b2 b3 b4 b5 b6 b7 b8,
  (p == p1) = false ->
  (p == p2) = false ->
  (p == p3) = false ->
  (p == p4) = false ->
  (p == p5) = false ->
  (p == p6) = false ->
  (p == p7) = false ->
  (p == p8) = false ->
  digit (set_digit (set_digit (set_digit (set_digit
        (set_digit (set_digit (set_digit (set_digit x p1 b1) p2 b2) p3 b3) p4 b4) 
         p5 b5) p6 b6) p7 b7) p8 b8) p = digit x p.
Proof.
 intros;repeat (rewrite get_set_diff;trivial).
Qed.

Definition of_Int31 x := 
 Eval lazy beta iota delta [nfold size sub31] in
 snd (Int31_rect (fun _ => (int31 * int31)%type)
   (nfold _ _ (fun b (res:int31 * int31) =>
                let (pos, i) := res in
                (pos-1, set_digit i pos b)) (30,0) size) x).

Lemma to_of_Int31 : forall x, to_Int31 (of_Int31 x) = x.
Proof.
 destruct x.
 unfold of_Int31;simpl.
 unfold to_Int31.
 Time repeat ((rewrite get_set_same;[ | reflexivity]) ||
         (rewrite get_set8_diff;[ | reflexivity | reflexivity | reflexivity | reflexivity
                                  | reflexivity | reflexivity | reflexivity | reflexivity ]) || 
         (rewrite get_set4_diff;[ | reflexivity | reflexivity | reflexivity | reflexivity ]) ||
         (rewrite get_set2_diff;[ | reflexivity | reflexivity ]) ||
         (rewrite get_set_diff;[| reflexivity])).
 trivial.
Time Qed.

Axiom to_Int31_inj : forall x y, to_Int31 x = to_Int31 y -> x = y.

Lemma of_to_Int31 : forall x, of_Int31 (to_Int31 x) = x.
Proof.
 intros;apply to_Int31_inj.
 rewrite to_of_Int31;trivial.
Qed.

Definition last_digit x :=
  Int31_rect (fun _ => bool) 
    (nfold _ _ (fun d last => d) false size) x.

Definition Digit x n :=
  last_digit (foldi _ (fun _ => shiftr) 1 n x).

Lemma all_Digit_same : forall x y,
  foldi _ (fun i P => Digit x i = Digit y i -> P) 0 30 (x = y).
Proof.
 cbv beta delta [foldi foldi_cont31].
 destruct x;destruct y;compute;intros;subst;trivial.
Qed.


Lemma all_digit_same : 
  forall x y,
  foldi _ (fun i P => digit x i = digit y i -> P) 0 30 (x = y).
Proof.
 cbv beta delta [foldi foldi_cont31];intros.
 apply to_Int31_inj.
 unfold to_Int31.
 repeat match goal with [H:_ = _ |- _ ] => rewrite H;clear H end;trivial.
Qed.




  


Lemma titi : forall x, Digit (to_Int31 x) 0 = digit x 0.
Proof.
 unfold to_Int31.
 compute;trivial.
Qed.

Lemma titi1 : forall x, Digit (to_Int31 x) 1 = digit x 1.
Proof.
 unfold to_Int31.
 compute;trivial.
Qed.

true.
Proof.
 destruct x
;simpl.

 


Axiom set_get_same : set_digit (get_digit x

 
  

Definition nth_int31 A (l:list A) (n:int31) (a:A) :=
 foldi_cont31 _ _ (fun _ cont l => cont (List.tl l)) 1 n (List.hd a) l.

Eval compute in nth_int31 _ (0::1::2::@nil int31) 0 5.



let i := 0 in
   let i := set_digit i 30 d30 in
   let i := set_digit i 29 d29 in
   let i := set_digit i 28 d28 in
   let i := set_digit i 27 d27 in
   let i := set_digit i 26 d26 in
   let i := set_digit i 25 d25 in
   let i := set_digit i 24 d24 in
   let i := set_digit i 23 d23 in
   let i := set_digit i 22 d22 in
   let i := set_digit i 21 d21 in
   let i := set_digit i 20 d20 in
   let i := set_digit i 19 d19 in
   let i := set_digit i 18 d18 in
   let i := set_digit i 17 d17 in
   let i := set_digit i 16 d16 in
   let i := set_digit i 15 d15 in
   let i := set_digit i 14 d14 in
   let i := set_digit i 13 d13 in
   let i := set_digit i 12 d12 in
   let i := set_digit i 11 d11 in
   let i := set_digit i 10 d10 in
   let i := set_digit i 9 d9 in
   let i := set_digit i 8 d8 in
   let i := set_digit i 7 d7 in
   let i := set_digit i 6 d6 in
   let i := set_digit i 5 d5 in
   let i := set_digit i 4 d4 in
   let i := set_digit i 3 d3 in
   let i := set_digit i 2 d2 in
   let i := set_digit i 1 d1 in
   let i := set_digit i 0 d0 in
   i
 end.

Evak compute in 

Definition foldi_down A (f:int31 -> A -> A) from downto :=
  foldi_down_cont31 A A (fun i cont a => cont (f i a)) from downto (fun a => a).

Eval compute 


Require Import NaryFunctions.

Fixpoint nprod_map2 (A B C:Type) (f:A->B->C) n : A^n -> B^n -> C^n :=
 match n as n0 return A^n0 -> B^n0 -> C^n0 with
 | O => fun _ _ => tt
 | S n => 
   fun ap bp =>
     let (a,pa) := ap in
     let (b,pb) := bp in
     (f a b, nprod_map2 A B C f n pa pb)
 end.

Definition nfun_map2 (A B C D:Type) (f:A->B->C) n (construct:C^^n --> D) : A^^n --> (B^^n --> D).
apply ncurry; intros pa.
apply ncurry; intros pb .
apply (nuncurry _ _ n construct (nprod_map2 _ _ _ f n pa pb)).
Defined.

Definition digits31_type t := Eval compute in nfun bool size t.

Inductive Int31 : Type := I31 : digits31_type Int31.
Check Int31_rect.
(*Check (Int31_rect (fun _ => Int31) (Int31_rect (fun _ => bool ^^ size --> Int31) (nfun_map2 _ _ _ _ andb size I31))).
*)
Definition Iland (x y:Int31) :=
 Int31_rect (fun _ => Int31) (Int31_rect _ (nfun_map2 _ _ _ _ andb size I31) x) y.

Definition Ilor (x y : Int31) :=
 Int31_rect (fun _ => Int31) (Int31_rect _ (nfun_map2 _ _ _ _ orb size I31) x) y.

Definition to_Int31 x : Int31 := 
 I31 
  (digit x 30)
  (digit x 29) (digit x 28) (digit x 27) (digit x 26) (digit x 25) 
  (digit x 24) (digit x 23) (digit x 22) (digit x 21) (digit x 20)
  (digit x 19) (digit x 18) (digit x 17) (digit x 16) (digit x 15) 
  (digit x 14) (digit x 13) (digit x 12) (digit x 11) (digit x 10)
  (digit x 9) (digit x 8) (digit x 7) (digit x 6) (digit x 5) 
  (digit x 4) (digit x 3) (digit x 2) (digit x 1) (digit x 0).

Parameter set_digit : int31 -> int31 -> bool -> int31.
Axiom get_set_same : forall x p b,
  ( (0 <= p) && (p < digits))%bool = true ->
  digit (set_digit x p b) p = b.
Axiom get_set_diff : forall x p1 p2 b,
  (p1 == p2) = false ->
  digit (set_digit x p1 b) p2 = digit x p2.

Definition of_Int31 x := 
 match x with
 | I31 d30 d29 d28 d27 d26 d25 d24 d23 d22 d21 d20 d19 d18 d17 d16
       d15 d14 d13 d12 d11 d10 d9 d8 d7 d6 d5 d4 d3 d2 d1 d0 =>
   let i := 0 in
   let i := set_digit i 30 d30 in
   let i := set_digit i 29 d29 in
   let i := set_digit i 28 d28 in
   let i := set_digit i 27 d27 in
   let i := set_digit i 26 d26 in
   let i := set_digit i 25 d25 in
   let i := set_digit i 24 d24 in
   let i := set_digit i 23 d23 in
   let i := set_digit i 22 d22 in
   let i := set_digit i 21 d21 in
   let i := set_digit i 20 d20 in
   let i := set_digit i 19 d19 in
   let i := set_digit i 18 d18 in
   let i := set_digit i 17 d17 in
   let i := set_digit i 16 d16 in
   let i := set_digit i 15 d15 in
   let i := set_digit i 14 d14 in
   let i := set_digit i 13 d13 in
   let i := set_digit i 12 d12 in
   let i := set_digit i 11 d11 in
   let i := set_digit i 10 d10 in
   let i := set_digit i 9 d9 in
   let i := set_digit i 8 d8 in
   let i := set_digit i 7 d7 in
   let i := set_digit i 6 d6 in
   let i := set_digit i 5 d5 in
   let i := set_digit i 4 d4 in
   let i := set_digit i 3 d3 in
   let i := set_digit i 2 d2 in
   let i := set_digit i 1 d1 in
   let i := set_digit i 0 d0 in
   i
 end.

Lemma to_of_Int31 : forall x, to_Int31 (of_Int31 x) = x.
Proof.
 destruct x;unfold to_Int31;simpl.
 repeat ((rewrite get_set_same;[ | reflexivity]) || (rewrite get_set_diff;[| reflexivity])). 



x p b 

Definition sneakr : bool -> Int31 -> Int31 := Eval compute in
 fun b => Int31_rect _ (napply_except_last _ _ (size-1) (I31 b)).

(** [sneakl b x] shifts [x] to the left by one bit.
   Leftmost digit is lost while rightmost digit becomes [b].
   Pseudo-code is
    [ match x with (I31 d0 ... dN) => I31 d1 ... dN b end ]
*)

Definition sneakl : bool -> Int31 -> Int31 := Eval compute in
 fun b => Int31_rect _ (fun _ => napply_then_last _ _ b (size-1) I31).


(** [shiftl], [shiftr], [twice] and [twice_plus_one] are direct
    consequences of [sneakl] and [sneakr]. *)

Definition shiftl := sneakl false.
Definition shiftr := sneakr false.
Definition twice := sneakl false.
Definition twice_plus_one := sneakl true.

Goal forall x,
  twice_plus_one x = Ilor (shiftl x) (to_Int31 1).
destruct x;intros.
set (T1 := to_Int31 1).
let t1 := eval compute in T1 in assert (T1 = t1) by reflexivity.
rewrite H.
simpl.
unfold nfun_map2, size;simpl.
repeat rewrite Bool.orb_false_r;trivial.

compute in (to_Int31 1).


set (pc := nprod_map2 _ _ _ f n pa pb).





SearchAbout nprod.
Definition nfun_map2 : forall (A B C D:Type) n (f:nfun C n D), nfun A n (nfun B n D).
intros A B C D. 
fix toto 1.
intros n;case n;simpl.
exact (fun d => d).
intros n0 fD a.
apply ncurry.
SearchAbout nfun.
Print ncurry.



  
Class Int31 := {
  d30 : bool;
  d29 : bool;
  d28 : bool;
  d27 : bool;
  d26 : bool;
  d25 : bool;
  d24 : bool;
  d23 : bool;
  d22 : bool;
  d21 : bool;
  d20 : bool;
  d19 : bool;
  d18 : bool;
  d17 : bool;
  d16 : bool;
  d15 : bool;
  d14 : bool;
  d13 : bool;
  d12 : bool;
  d11 : bool;
  d10 : bool;
  d9  : bool;
  d8  : bool;
  d7  : bool;
  d6  : bool;
  d5  : bool;
  d4  : bool;
  d3  : bool;
  d2  : bool;
  d1  : bool;
  d0  : bool
}.

Instance to_Int31 x : Int31 := {
  d30 := digit x 30;
  d29 := digit x 29;
  d28 := digit x 28;
  d27 := digit x 27;
  d26 := digit x 26;
  d25 := digit x 25;
  d24 := digit x 24;
  d23 := digit x 23;
  d22 := digit x 22;
  d21 := digit x 21;
  d20 := digit x 20;
  d19 := digit x 19;
  d18 := digit x 18;
  d17 := digit x 17;
  d16 := digit x 16;
  d15 := digit x 15;
  d14 := digit x 14;
  d13 := digit x 13;
  d12 := digit x 12;
  d11 := digit x 11;
  d10 := digit x 10; 
  d9  := digit x 9;
  d8  := digit x 8;
  d7  := digit x 7;
  d6  := digit x 6;
  d5  := digit x 5;
  d4  := digit x 4;
  d3  := digit x 3;
  d2  := digit x 2;
  d1  := digit x 1;
  d0  := digit x 0
}.

Definition of_Int31 (X:Int31) :=
 let (d30,d29,d28,d27,d26,d25,d24,d23,d22,d21,d20,
          d19,d18,d17,d16,d15,d14,d13,d12,d11,d10,
          d9,d8,d7,d6,d5,d4,d3,d2,d1,d0) := X in
 (mk_digit d30 30) lor
 (mk_digit d29 29) lor
 (mk_digit d28 28) lor
 (mk_digit d27 27) lor
 (mk_digit d26 26) lor
 (mk_digit d25 25) lor
 (mk_digit d24 24) lor
 (mk_digit d23 23) lor
 (mk_digit d22 22) lor
 (mk_digit d21 21) lor
 (mk_digit d20 20) lor
 (mk_digit d19 19) lor
 (mk_digit d18 18) lor
 (mk_digit d17 17) lor
 (mk_digit d16 16) lor
 (mk_digit d15 15) lor
 (mk_digit d14 14) lor
 (mk_digit d13 13) lor
 (mk_digit d12 12) lor
 (mk_digit d11 11) lor
 (mk_digit d10 10) lor
 (mk_digit d9 9) lor
 (mk_digit d8 8) lor
 (mk_digit d7 7) lor
 (mk_digit d6 6) lor
 (mk_digit d5 5) lor
 (mk_digit d4 4) lor
 (mk_digit d3 3) lor
 (mk_digit d2 2) lor
 (mk_digit d1 1) lor
 (mk_digit d0 0).

Lemma to_of_Int31 : forall x, of_Int31 (to_Int31 x) = x.
Proof.
 unfold to_Int31, of_Int31.
 unfold mk_digit, digit.
simpl.

 lor

 match X with
 | 
Definition get_digits x := 
  digit x 0 ::
  digit x 1 ::
  digit x 2 ::
  digit x 3 ::
  digit x 4 ::
  digit x 5 ::
  digit x 6 ::
  digit x 7 ::
  digit x 8 ::
  digit x 9 ::
  digit x 10 ::
  digit x 11 ::
  digit x 12 ::
  digit x 13 ::
  digit x 14 ::
  digit x 15 ::
  digit x 16 ::
  digit x 17 ::
  digit x 18 ::
  digit x 19 ::
  digit x 20 ::
  digit x 21 ::
  digit x 22 ::
  digit x 23 ::
  digit x 24 ::
  digit x 25 ::
  digit x 26 ::
  digit x 27 ::
  digit x 28 ::
  digit x 29 ::
  digit x 30 :: nil.

*)