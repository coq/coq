(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import Utf8.
Require Export DoubleType.
Require Import Lia.
Require Import Zpow_facts.
Require Import Zgcd_alt.
Import Znumtheory.

Register bool as kernel.ind_bool.
Register prod as kernel.ind_pair.
Register carry as kernel.ind_carry.
Register comparison as kernel.ind_cmp.

Definition size := 63%nat.

Primitive int := #int63_type.
Register int as num.int63.type.
Declare Scope int63_scope.
Definition id_int : int -> int := fun x => x.
Declare ML Module "int63_syntax_plugin".

Delimit Scope int63_scope with int63.
Bind Scope int63_scope with int.

(* Logical operations *)
Primitive lsl := #int63_lsl.
Infix "<<" := lsl (at level 30, no associativity) : int63_scope.

Primitive lsr := #int63_lsr.
Infix ">>" := lsr (at level 30, no associativity) : int63_scope.

Primitive land := #int63_land.
Infix "land" := land (at level 40, left associativity) : int63_scope.

Primitive lor := #int63_lor.
Infix "lor" := lor (at level 40, left associativity) : int63_scope.

Primitive lxor := #int63_lxor.
Infix "lxor" := lxor (at level 40, left associativity) : int63_scope.

(* Arithmetic modulo operations *)
Primitive add := #int63_add.
Notation "n + m" := (add n m) : int63_scope.

Primitive sub := #int63_sub.
Notation "n - m" := (sub n m) : int63_scope.

Primitive mul := #int63_mul.
Notation "n * m" := (mul n m) : int63_scope.

Primitive mulc := #int63_mulc.

Primitive div := #int63_div.
Notation "n / m" := (div n m) : int63_scope.

Primitive mod := #int63_mod.
Notation "n '\%' m" := (mod n m) (at level 40, left associativity) : int63_scope.

(* Comparisons *)
Primitive eqb := #int63_eq.
Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int63_scope.

Primitive ltb := #int63_lt.
Notation "m < n" := (ltb m n) : int63_scope.

Primitive leb := #int63_le.
Notation "m <= n" := (leb m n) : int63_scope.
Notation "m ≤ n" := (leb m n) (at level 70, no associativity) : int63_scope.

Local Open Scope int63_scope.

(** The number of digits as a int *)
Definition digits := 63.

(** The bigger int *)
Definition max_int := Eval vm_compute in 0 - 1.
Register Inline max_int.

(** Access to the nth digits *)
Definition get_digit x p := (0 < (x land (1 << p))).

Definition set_digit x p (b:bool) :=
  if if 0 <= p then p < digits else false then
    if b then x lor (1 << p)
    else x land (max_int lxor (1 << p))
  else x.

(** Equality to 0 *)
Definition is_zero (i:int) := i == 0.
Register Inline is_zero.

(** Parity *)
Definition is_even (i:int) := is_zero (i land 1).
Register Inline is_even.

(** Bit *)

Definition bit i n :=  negb (is_zero ((i >> n) << (digits - 1))).
(* Register bit as PrimInline. *)

(** Extra modulo operations *)
Definition opp (i:int) := 0 - i.
Register Inline opp.
Notation "- x" := (opp x) : int63_scope.

Definition oppcarry i := max_int - i.
Register Inline oppcarry.

Definition succ i := i + 1.
Register Inline succ.

Definition pred i := i - 1.
Register Inline pred.

Definition addcarry i j := i + j + 1.
Register Inline addcarry.

Definition subcarry i j := i - j - 1.
Register Inline subcarry.

(** Exact arithmetic operations *)

Definition addc_def x y :=
  let r := x + y in
  if r < x then C1 r else C0 r.
(* the same but direct implementation for effeciancy *)
Primitive addc := #int63_addc.
Notation "n '+c' m" := (addc n m) (at level 50, no associativity) : int63_scope.

Definition addcarryc_def x y :=
  let r := addcarry x y in
  if r <= x then C1 r else C0 r.
(* the same but direct implementation for effeciancy *)
Primitive addcarryc := #int63_addcarryc.

Definition subc_def x y :=
  if y <= x then C0 (x - y) else C1 (x - y).
(* the same but direct implementation for effeciancy *)
Primitive subc := #int63_subc.
Notation "n '-c' m" := (subc n m) (at level 50, no associativity) : int63_scope.

Definition subcarryc_def x y :=
  if y < x then C0 (x - y - 1) else C1 (x - y - 1).
(* the same but direct implementation for effeciancy *)
Primitive subcarryc := #int63_subcarryc.

Definition diveucl_def x y := (x/y, x\%y).
(* the same but direct implementation for effeciancy *)
Primitive diveucl := #int63_diveucl.

Primitive diveucl_21 := #int63_div21.

Definition addmuldiv_def p x y :=
  (x << p) lor (y >> (digits - p)).
Primitive addmuldiv := #int63_addmuldiv.

Definition oppc (i:int) := 0 -c i.
Register Inline oppc.

Definition succc i := i +c 1.
Register Inline succc.

Definition predc i := i -c 1.
Register Inline predc.

(** Comparison *)
Definition compare_def x y :=
  if x < y then Lt
  else if (x == y) then Eq else Gt.

Primitive compare := #int63_compare.
Notation "n ?= m" := (compare n m) (at level 70, no associativity) : int63_scope.

Import Bool ZArith.
(** Translation to Z *)
Fixpoint to_Z_rec (n:nat) (i:int) :=
  match n with
  | O => 0%Z
  | S n =>
    (if is_even i then Z.double else Zdouble_plus_one) (to_Z_rec n (i >> 1))
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

Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99) : int63_scope.

Definition wB := (2 ^ (Z.of_nat size))%Z.

Lemma to_Z_rec_bounded size : forall x, (0 <= to_Z_rec size x < 2 ^ Z.of_nat size)%Z.
Proof.
 elim size. simpl; auto with zarith.
 intros n ih x; rewrite inj_S; simpl; assert (W := ih (x >> 1)%int63).
 rewrite Z.pow_succ_r; auto with zarith.
 destruct (is_even x).
   rewrite Zdouble_mult; auto with zarith.
 rewrite Zdouble_plus_one_mult; auto with zarith.
Qed.

Corollary to_Z_bounded : forall x, (0 <= [| x |] < wB)%Z.
Proof. apply to_Z_rec_bounded. Qed.

(* =================================================== *)
Local Open Scope Z_scope.
(* General arithmetic results *)
Lemma Z_lt_div2 x y : x < 2 * y -> x / 2 < y.
Proof. apply Z.div_lt_upper_bound; reflexivity. Qed.

Theorem Zmod_le_first a b : 0 <= a -> 0 < b -> 0 <= a mod b <= a.
Proof.
  intros ha hb; case (Z_mod_lt a b); [ auto with zarith | ]; intros p q; apply (conj p).
  case (Z.le_gt_cases b a). lia.
  intros hlt; rewrite Zmod_small; lia.
Qed.

Theorem Zmod_distr: forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
  (2 ^a * r + t) mod (2 ^ b) = (2 ^a * r) mod (2 ^ b) + t.
Proof.
  intros a b r t (H1, H2) H3 (H4, H5).
  assert (t < 2 ^ b).
  apply Z.lt_le_trans with (1:= H5); auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  rewrite Zplus_mod; auto with zarith.
  rewrite -> Zmod_small with (a := t); auto with zarith.
  apply Zmod_small; auto with zarith.
  split; auto with zarith.
  assert (0 <= 2 ^a * r); auto with zarith.
  apply Z.add_nonneg_nonneg; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end;
   auto with zarith.
  pattern (2 ^ b) at 2; replace (2 ^ b) with ((2 ^ b - 2 ^a) + 2 ^ a);
    try ring.
  apply Z.add_le_lt_mono; auto with zarith.
  replace b with ((b - a) + a); try ring.
  rewrite Zpower_exp; auto with zarith.
  pattern (2 ^a) at 4; rewrite <- (Z.mul_1_l (2 ^a));
   try rewrite <- Z.mul_sub_distr_r.
  rewrite (Z.mul_comm (2 ^(b - a))); rewrite  Zmult_mod_distr_l;
   auto with zarith.
  rewrite (Z.mul_comm (2 ^a)); apply Z.mul_le_mono_nonneg_r; auto with zarith.
  match goal with |- context [?X mod ?Y] => case (Z_mod_lt X Y) end.
    apply Z.lt_gt; auto with zarith.
    auto with zarith.
Qed.

(* Results about pow2 *)
Lemma pow2_pos n : 0 <= n → 2 ^ n > 0.
Proof. intros h; apply Z.lt_gt, Zpower_gt_0; lia. Qed.

Lemma pow2_nz n : 0 <= n → 2 ^ n ≠ 0.
Proof. intros h; generalize (pow2_pos _ h); lia. Qed.

Hint Resolve pow2_pos pow2_nz : zarith.

(* =================================================== *)

(** Trivial lemmas without axiom *)

Lemma wB_diff_0 : wB <> 0.
Proof. exact (fun x => let 'eq_refl := x in idProp). Qed.

Lemma wB_pos : 0 < wB.
Proof. reflexivity. Qed.

Lemma to_Z_0 : [|0|] = 0.
Proof. reflexivity. Qed.

Lemma to_Z_1 : [|1|] = 1.
Proof. reflexivity. Qed.

(* Notations *)
Local Open Scope Z_scope.

Notation "[+| c |]" :=
   (interp_carry 1 wB to_Z c)  (at level 0, c at level 99) : int63_scope.

Notation "[-| c |]" :=
   (interp_carry (-1) wB to_Z c)  (at level 0, c at level 99) : int63_scope.

Notation "[|| x ||]" :=
   (zn2z_to_Z wB to_Z x)  (at level 0, x at level 99) : int63_scope.

(* Bijection : int63 <-> Bvector size *)

Axiom of_to_Z : forall x, of_Z [| x |] = x.

Notation "'φ' x" := [| x |] (at level 0) : int63_scope.

Lemma can_inj {rT aT} {f: aT -> rT} {g: rT -> aT} (K: forall a, g (f a) = a) {a a'} (e: f a = f a') : a = a'.
Proof. generalize (K a) (K a'). congruence. Qed.

Lemma to_Z_inj x y : φ x = φ y → x = y.
Proof. exact (λ e, can_inj of_to_Z e). Qed.

(** Specification of logical operations *)
Local Open Scope Z_scope.
Axiom lsl_spec : forall x p, [| x << p |] = [| x |] * 2 ^ [| p |] mod wB.

Axiom lsr_spec : forall x p, [|x >> p|] = [|x|] / 2 ^ [|p|].

Axiom land_spec: forall x y i , bit (x land y) i = bit x i && bit y i.

Axiom lor_spec: forall x y i, bit (x lor y) i = bit x i || bit y i.

Axiom lxor_spec: forall  x y i, bit (x lxor y) i = xorb (bit x i) (bit y i).

(** Specification of basic opetations *)

(* Arithmetic modulo operations *)

(* Remarque : les axiomes seraient plus simple si on utilise of_Z a la place :
   exemple : add_spec : forall x y, of_Z (x + y) = of_Z x + of_Z y. *)

Axiom add_spec : forall x y, [|x + y|] = ([|x|] + [|y|]) mod wB.

Axiom sub_spec : forall x y, [|x - y|] = ([|x|] - [|y|]) mod wB.

Axiom mul_spec : forall x y, [| x * y |]  = [|x|] * [|y|] mod wB.

Axiom mulc_spec : forall x y, [|x|] * [|y|] = [|fst (mulc x y)|] * wB + [|snd (mulc x y)|].

Axiom div_spec : forall x y, [|x / y|] = [|x|] / [|y|].

Axiom mod_spec : forall x y, [|x \% y|] = [|x|] mod [|y|].

(* Comparisons *)
Axiom eqb_correct : forall i j, (i == j)%int63 = true -> i = j.

Axiom eqb_refl : forall x, (x == x)%int63 = true.

Axiom ltb_spec : forall x y, (x < y)%int63 = true <-> [|x|] < [|y|].

Axiom leb_spec : forall x y, (x <= y)%int63 = true <-> [|x|] <= [|y|].

(** Exotic operations *)

(** I should add the definition (like for compare) *)
Primitive head0 := #int63_head0.
Primitive tail0 := #int63_tail0.

(** Axioms on operations which are just short cut *)

Axiom compare_def_spec : forall x y, compare x y = compare_def x y.

Axiom head0_spec  : forall x,  0 < [|x|] ->
         wB/ 2 <= 2 ^ ([|head0 x|]) * [|x|] < wB.

Axiom tail0_spec  : forall x, 0 < [|x|] ->
         (exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail0 x|]))%Z.

Axiom addc_def_spec : forall x y, (x +c y)%int63 = addc_def x y.

Axiom addcarryc_def_spec : forall x y, addcarryc x y = addcarryc_def x y.

Axiom subc_def_spec : forall x y, (x -c y)%int63 = subc_def x y.

Axiom subcarryc_def_spec : forall x y, subcarryc x y = subcarryc_def x y.

Axiom diveucl_def_spec : forall x y, diveucl x y = diveucl_def x y.

Axiom diveucl_21_spec :  forall a1 a2 b,
   let (q,r) := diveucl_21 a1 a2 b in
   let (q',r') := Z.div_eucl ([|a1|] * wB + [|a2|]) [|b|] in
   [|q|] = Z.modulo q' wB /\ [|r|] = r'.

Axiom addmuldiv_def_spec : forall p x y,
  addmuldiv p x y = addmuldiv_def p x y.

(** Square root functions using newton iteration **)
Local Open Scope int63_scope.

Definition sqrt_step (rec: int -> int -> int) (i j: int) :=
  let quo := i / j in
  if quo < j then rec i ((j + quo) >> 1)
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

Definition high_bit := 1 << (digits - 1).

Definition sqrt2_step (rec: int -> int -> int -> int)
   (ih il j: int)  :=
  if ih < j then
    let (quo,_) := diveucl_21 ih il j in
    if quo < j then
      match j +c quo with
      | C0 m1 => rec ih il (m1 >> 1)
      | C1 m1 => rec ih il ((m1 >> 1) + high_bit)
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

(** Gcd **)
Fixpoint gcd_rec (guard:nat) (i j:int) {struct guard} :=
   match guard with
   | O => 1
   | S p => if j == 0 then i else gcd_rec p j (i \% j)
   end.

Definition gcd := gcd_rec (2*size).

(** equality *)
Lemma eqb_complete : forall x y, x = y -> (x == y) = true.
Proof.
 intros x y H; rewrite -> H, eqb_refl;trivial.
Qed.

Lemma eqb_spec : forall x y, (x == y) = true <-> x = y.
Proof.
 split;auto using eqb_correct, eqb_complete.
Qed.

Lemma eqb_false_spec : forall x y, (x == y) = false <-> x <> y.
Proof.
 intros;rewrite <- not_true_iff_false, eqb_spec;split;trivial.
Qed.

Lemma eqb_false_complete : forall x y, x <> y -> (x == y) = false.
Proof.
 intros x y;rewrite eqb_false_spec;trivial.
Qed.

Lemma eqb_false_correct : forall x y, (x == y) = false -> x <> y.
Proof.
 intros x y;rewrite eqb_false_spec;trivial.
Qed.

Definition eqs (i j : int) : {i = j} + { i <> j } :=
  (if i == j as b return ((b = true -> i = j) -> (b = false -> i <> j) -> {i=j} + {i <> j} )
    then fun (Heq : true = true -> i = j) _ => left _ (Heq (eq_refl true))
    else fun _ (Hdiff : false = false -> i <> j) => right _ (Hdiff (eq_refl false)))
  (eqb_correct i j)
  (eqb_false_correct i j).

Lemma eq_dec : forall i j:int, i = j \/ i <> j.
Proof.
 intros i j;destruct (eqs i j);auto.
Qed.

(* Extra function on equality *)

Definition cast i j :=
     (if i == j as b return ((b = true -> i = j) -> option (forall P : int -> Type, P i -> P j))
      then fun Heq : true = true -> i = j =>
             Some
             (fun (P : int -> Type) (Hi : P i) =>
               match Heq (eq_refl true) in (_ = y) return (P y) with
               | eq_refl => Hi
               end)
      else fun _ : false = true -> i = j => None) (eqb_correct i j).

Lemma cast_refl : forall i, cast i i = Some (fun P H => H).
Proof.
 unfold cast;intros.
 generalize (eqb_correct i i).
 rewrite eqb_refl;intros.
 rewrite (Eqdep_dec.eq_proofs_unicity eq_dec (e (eq_refl true)) (eq_refl i));trivial.
Qed.

Lemma cast_diff : forall i j, i == j = false -> cast i j = None.
Proof.
 intros;unfold cast;intros; generalize (eqb_correct i j).
 rewrite H;trivial.
Qed.

Definition eqo i j :=
   (if i == j as b return ((b = true -> i = j) -> option (i=j))
    then fun Heq : true = true -> i = j =>
             Some (Heq (eq_refl true))
     else fun _ : false = true -> i = j => None) (eqb_correct i j).

Lemma eqo_refl : forall i, eqo i i = Some (eq_refl i).
Proof.
 unfold eqo;intros.
 generalize (eqb_correct i i).
 rewrite eqb_refl;intros.
 rewrite (Eqdep_dec.eq_proofs_unicity eq_dec (e (eq_refl true)) (eq_refl i));trivial.
Qed.

Lemma eqo_diff : forall i j, i == j = false -> eqo i j = None.
Proof.
 unfold eqo;intros; generalize (eqb_correct i j).
 rewrite H;trivial.
Qed.

(** Comparison *)

Lemma eqbP x y : reflect ([| x |] = [| y |]) (x == y).
Proof. apply iff_reflect; rewrite eqb_spec; split; [ apply to_Z_inj | apply f_equal ]. Qed.

Lemma ltbP x y : reflect ([| x |] < [| y |])%Z (x < y).
Proof. apply iff_reflect; symmetry; apply ltb_spec. Qed.

Lemma lebP x y : reflect ([| x |] <= [| y |])%Z (x ≤ y).
Proof. apply iff_reflect; symmetry; apply leb_spec. Qed.

Lemma compare_spec x y : compare x y = ([|x|] ?= [|y|])%Z.
Proof.
  rewrite compare_def_spec; unfold compare_def.
  case ltbP; [ auto using Z.compare_lt_iff | intros hge ].
  case eqbP; [ now symmetry; apply Z.compare_eq_iff | intros hne ].
  symmetry; apply Z.compare_gt_iff; lia.
Qed.

Lemma is_zero_spec x : is_zero x = true <-> x = 0%int63.
Proof. apply eqb_spec. Qed.

Lemma diveucl_spec x y :
  let (q,r) := diveucl x y in
  ([| q |], [| r |]) = Z.div_eucl [| x |] [| y |].
Proof.
 rewrite diveucl_def_spec; unfold diveucl_def; rewrite div_spec, mod_spec; unfold Z.div, Zmod.
 destruct (Z.div_eucl [| x |] [| y |]); trivial.
Qed.

Local Open Scope Z_scope.
(** Addition *)
Lemma addc_spec x y : [+| x +c y |] = [| x |] + [| y |].
Proof.
  rewrite addc_def_spec; unfold addc_def, interp_carry.
  pose proof (to_Z_bounded x); pose proof (to_Z_bounded y).
  case ltbP; rewrite add_spec.
    case (Z_lt_ge_dec ([| x |] + [| y |]) wB).
      intros k; rewrite Zmod_small; lia.
    intros hge; rewrite <- (Zmod_unique _ _ 1 ([| x |] + [| y |] - wB)); lia.
 case (Z_lt_ge_dec ([| x |] + [| y |]) wB).
   intros k; rewrite Zmod_small; lia.
 intros hge; rewrite <- (Zmod_unique _ _ 1 ([| x |] + [| y |] - wB)); lia.
Qed.

Lemma succ_spec x : [| succ x |] = ([| x |] + 1) mod wB.
Proof. apply add_spec. Qed.

Lemma succc_spec x : [+| succc x |] = [| x |] + 1.
Proof. apply addc_spec. Qed.

Lemma addcarry_spec x y : [| addcarry x y |] = ([| x |] + [| y |] + 1) mod wB.
Proof. unfold addcarry; rewrite -> !add_spec, Zplus_mod_idemp_l; trivial. Qed.

Lemma addcarryc_spec x y : [+| addcarryc x y |] = [| x |] + [| y |] + 1.
Proof.
  rewrite addcarryc_def_spec; unfold addcarryc_def, interp_carry.
  pose proof (to_Z_bounded x); pose proof (to_Z_bounded y).
  case lebP; rewrite addcarry_spec.
    case (Z_lt_ge_dec ([| x |] + [| y |] + 1) wB).
      intros hlt; rewrite Zmod_small; lia.
    intros hge; rewrite <- (Zmod_unique _ _ 1 ([| x |] + [| y |] + 1 - wB)); lia.
  case (Z_lt_ge_dec ([| x |] + [| y |] + 1) wB).
    intros hlt; rewrite Zmod_small; lia.
  intros hge; rewrite <- (Zmod_unique _ _ 1 ([| x |] + [| y |] + 1 - wB)); lia.
Qed.

(** Subtraction *)
Lemma subc_spec x y : [-| x -c y |] = [| x |] - [| y |].
Proof.
  rewrite subc_def_spec; unfold subc_def; unfold interp_carry.
  pose proof (to_Z_bounded x); pose proof (to_Z_bounded y).
  case lebP.
    intros hle; rewrite sub_spec, Z.mod_small; lia.
  intros hgt; rewrite sub_spec, <- (Zmod_unique _ wB (-1) ([| x |] - [| y |] + wB)); lia.
Qed.

Lemma pred_spec x : [| pred x |] = ([| x |] - 1) mod wB.
Proof. apply sub_spec. Qed.

Lemma predc_spec x : [-| predc x |] = [| x |] - 1.
Proof. apply subc_spec. Qed.

Lemma oppc_spec x : [-| oppc x |] = - [| x |].
Proof. unfold oppc; rewrite -> subc_spec, to_Z_0; trivial. Qed.

Lemma opp_spec x : [|- x |] = - [| x |] mod wB.
Proof. unfold opp; rewrite -> sub_spec, to_Z_0; trivial. Qed.

Lemma oppcarry_spec x : [| oppcarry x |] = wB - [| x |] - 1.
Proof.
 unfold oppcarry; rewrite sub_spec.
 rewrite <- Zminus_plus_distr, Zplus_comm, Zminus_plus_distr.
 apply Zmod_small.
 generalize (to_Z_bounded x); auto with zarith.
Qed.

Lemma subcarry_spec x y : [| subcarry x y |] = ([| x |] - [| y |] - 1) mod wB.
Proof. unfold subcarry; rewrite !sub_spec, Zminus_mod_idemp_l; trivial. Qed.

Lemma subcarryc_spec x y : [-| subcarryc x y |] = [| x |] - [| y |] - 1.
Proof.
  rewrite subcarryc_def_spec; unfold subcarryc_def, interp_carry; fold (subcarry x y).
 pose proof (to_Z_bounded x); pose proof (to_Z_bounded y).
 case ltbP; rewrite subcarry_spec.
   intros hlt; rewrite Zmod_small; lia.
 intros hge; rewrite <- (Zmod_unique _ _ (-1) ([| x |] - [| y |] - 1 + wB)); lia.
Qed.

(** GCD *)
Lemma to_Z_gcd : forall i j, [| gcd i j |] = Zgcdn (2 * size) [| j |] [| i |].
Proof.
 unfold gcd.
 elim (2*size)%nat. reflexivity.
 intros n ih i j; simpl.
 pose proof (to_Z_bounded j) as hj; pose proof (to_Z_bounded i).
 case eqbP; rewrite to_Z_0.
   intros ->; rewrite Z.abs_eq; lia.
 intros hne; rewrite ih; clear ih.
 rewrite <- mod_spec.
 revert hj hne; case [| j |]; intros; lia.
Qed.

Lemma gcd_spec a b : Zis_gcd [| a |] [| b |] [| gcd a b |].
Proof.
 rewrite to_Z_gcd.
 apply Zis_gcd_sym.
 apply Zgcdn_is_gcd.
 unfold Zgcd_bound.
 generalize (to_Z_bounded b).
 destruct [|b|].
 unfold size; auto with zarith.
 intros (_,H).
 cut (Psize p <= size)%nat; [ lia | rewrite <- Zpower2_Psize; auto].
 intros (H,_); compute in H; elim H; auto.
Qed.

(** Head0, Tail0 *)
Lemma head00_spec x : [| x |] = 0 -> [| head0 x |] = [| digits |].
Proof. now intros h; rewrite (to_Z_inj _ 0 h). Qed.

Lemma tail00_spec x : [| x |] = 0 -> [|tail0 x|] = [|digits|].
Proof. now intros h; rewrite (to_Z_inj _ 0 h). Qed.

Infix "≡" := (eqm wB) (at level 80) : int63_scope.

Lemma eqm_mod x y : x mod wB ≡ y mod wB → x ≡ y.
Proof.
  intros h.
  eapply (eqm_trans).
    apply eqm_sym; apply Zmod_eqm.
  apply (eqm_trans _ _ _ _ h).
  apply Zmod_eqm.
Qed.

Lemma eqm_sub x y : x ≡ y → x - y ≡ 0.
Proof. intros h; unfold eqm; rewrite Zminus_mod, h, Z.sub_diag; reflexivity. Qed.

Lemma eqmE x y : x ≡ y → ∃ k, x - y = k * wB.
Proof.
  intros h.
  exact (Zmod_divide (x - y) wB (λ e, let 'eq_refl := e in I) (eqm_sub _ _ h)).
Qed.

Lemma eqm_subE x y : x ≡ y ↔ x - y ≡ 0.
Proof.
  split. apply eqm_sub.
  intros h; case (eqmE _ _ h); clear h; intros q h.
  assert (y = x - q * wB) by lia.
  clear h; subst y.
  unfold eqm; rewrite Zminus_mod, Z_mod_mult, Z.sub_0_r, Zmod_mod; reflexivity.
Qed.

Lemma int_eqm x y : x = y → φ x ≡ φ y.
Proof. unfold eqm; intros ->; reflexivity. Qed.

Lemma eqmI x y : φ x ≡ φ y → x = y.
Proof.
  unfold eqm.
  repeat rewrite Zmod_small by apply to_Z_bounded.
  apply to_Z_inj.
Qed.

(* ADD *)
Lemma add_assoc x y z: (x + (y + z) = (x + y) + z)%int63.
Proof.
 apply to_Z_inj; rewrite !add_spec.
 rewrite -> Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zplus_assoc; auto.
Qed.

Lemma add_comm x y: (x + y = y + x)%int63.
Proof.
 apply to_Z_inj; rewrite -> !add_spec, Zplus_comm; auto.
Qed.

Lemma add_le_r m n:
  if  (n <= m + n)%int63 then  ([|m|] + [|n|] < wB)%Z else  (wB <= [|m|] + [|n|])%Z.
Proof.
 case (to_Z_bounded m); intros H1m H2m.
 case (to_Z_bounded n); intros H1n H2n.
 case (Zle_or_lt wB ([|m|] + [|n|])); intros H.
   assert (H1: ([| m + n |] = [|m|] + [|n|] - wB)%Z).
     rewrite add_spec.
     replace (([|m|] + [|n|]) mod wB)%Z with (((([|m|] + [|n|]) - wB) + wB) mod wB)%Z.
     rewrite -> Zplus_mod, Z_mod_same_full, Zplus_0_r, !Zmod_small; auto with zarith.
     rewrite !Zmod_small; auto with zarith.
     apply f_equal2 with (f := Zmod); auto with zarith.
   case_eq (n <= m + n)%int63; auto.
   rewrite leb_spec, H1; auto with zarith.
 assert (H1: ([| m + n |] = [|m|] + [|n|])%Z).
   rewrite add_spec, Zmod_small; auto with zarith.
 replace (n <= m + n)%int63 with true; auto.
 apply sym_equal; rewrite leb_spec, H1; auto with zarith.
Qed.

Lemma add_cancel_l x y z : (x + y = x + z)%int63 -> y = z.
Proof.
  intros h; apply int_eqm in h; rewrite !add_spec in h; apply eqm_mod, eqm_sub in h.
  replace (_ + _ - _) with (φ(y) - φ(z)) in h by lia.
  rewrite <- eqm_subE in h.
  apply eqmI, h.
Qed.

Lemma add_cancel_r x y z : (y + x = z + x)%int63 -> y = z.
Proof.
  rewrite !(fun t => add_comm t x); intros Hl; apply (add_cancel_l x); auto.
Qed.

Coercion b2i (b: bool) : int := if b then 1%int63 else 0%int63.

(* LSR *)
Lemma lsr0 i : 0 >> i = 0%int63.
Proof. apply to_Z_inj; rewrite lsr_spec; reflexivity. Qed.

Lemma lsr_0_r i: i >> 0 = i.
Proof. apply to_Z_inj; rewrite lsr_spec, Zdiv_1_r; exact eq_refl. Qed.

Lemma lsr_1 n : 1 >> n = (n == 0).
Proof.
  case eqbP.
    intros h; rewrite (to_Z_inj _ _ h), lsr_0_r; reflexivity.
 intros Hn.
 assert (H1n : (1 >> n = 0)%int63); auto.
 apply to_Z_inj; rewrite lsr_spec.
 apply Zdiv_small; rewrite to_Z_1; split; auto with zarith.
 change 1%Z with (2^0)%Z.
 apply Zpower_lt_monotone; split; auto with zarith.
 rewrite to_Z_0 in Hn.
 generalize (to_Z_bounded n).
 lia.
Qed.

Lemma lsr_add i m n: ((i >> m) >> n = if n <= m + n then i >> (m + n) else 0)%int63.
Proof.
 case (to_Z_bounded m); intros H1m H2m.
 case (to_Z_bounded n); intros H1n H2n.
 case (to_Z_bounded i); intros H1i H2i.
 generalize (add_le_r m n); case (n <= m + n)%int63; intros H.
   apply to_Z_inj; rewrite -> !lsr_spec, Zdiv_Zdiv, <- Zpower_exp; auto with zarith.
   rewrite add_spec, Zmod_small; auto with zarith.
 apply to_Z_inj; rewrite -> !lsr_spec, Zdiv_Zdiv, <- Zpower_exp; auto with zarith.
 apply Zdiv_small. split; [ auto with zarith | ].
 eapply Z.lt_le_trans; [ | apply Zpower2_le_lin ]; auto with zarith.
Qed.

Lemma lsr_add_distr x y n: (x + y) << n = ((x << n) + (y << n))%int63.
Proof.
 apply to_Z_inj.
 rewrite -> add_spec, !lsl_spec, add_spec.
 rewrite -> Zmult_mod_idemp_l, <-Zplus_mod.
 apply f_equal2 with (f := Zmod); auto with zarith.
Qed.

(* LSL *)
Lemma lsl0 i: 0 << i = 0%int63.
Proof.
 apply to_Z_inj.
 generalize (lsl_spec 0 i).
 rewrite to_Z_0, Zmult_0_l, Zmod_0_l; auto.
Qed.

Lemma lsl0_r i : i << 0 = i.
Proof.
 apply to_Z_inj.
 rewrite -> lsl_spec, to_Z_0, Z.mul_1_r.
 apply Zmod_small; apply (to_Z_bounded i).
Qed.

Lemma lsl_add_distr x y n: (x + y) << n = ((x << n) + (y << n))%int63.
Proof.
 apply to_Z_inj; rewrite -> !lsl_spec, !add_spec, Zmult_mod_idemp_l.
 rewrite -> !lsl_spec, <-Zplus_mod.
 apply f_equal2 with (f := Zmod); auto with zarith.
Qed.

Lemma lsr_M_r x i (H: (digits <= i = true)%int63) : x >> i = 0%int63.
Proof.
 apply to_Z_inj.
 rewrite lsr_spec, to_Z_0.
 case (to_Z_bounded x); intros H1x H2x.
 case (to_Z_bounded digits); intros H1d H2d.
 rewrite -> leb_spec in H.
 apply Zdiv_small; split; [ auto | ].
 apply (Z.lt_le_trans _ _ _ H2x).
 unfold wB; change (Z_of_nat size) with [|digits|].
 apply Zpower_le_monotone; auto with zarith.
Qed.

(* BIT *)
Lemma bit_0_spec i: [|bit i 0|] = [|i|] mod 2.
Proof.
 unfold bit, is_zero. rewrite lsr_0_r.
 assert (Hbi: ([|i|] mod 2 < 2)%Z).
   apply Z_mod_lt; auto with zarith.
 case (to_Z_bounded i); intros H1i H2i.
 case (Zmod_le_first [|i|] 2); auto with zarith; intros H3i H4i.
 assert (H2b: (0 < 2 ^ [|digits - 1|])%Z).
   apply Zpower_gt_0; auto with zarith.
   case (to_Z_bounded (digits -1)); auto with zarith.
 assert (H: [|i << (digits -1)|] = ([|i|] mod 2 * 2^ [|digits -1|])%Z).
 rewrite lsl_spec.
 rewrite -> (Z_div_mod_eq [|i|] 2) at 1; auto with zarith.
 rewrite -> Zmult_plus_distr_l, <-Zplus_mod_idemp_l.
 rewrite -> (Zmult_comm 2), <-Zmult_assoc.
 replace (2 * 2 ^ [|digits - 1|])%Z with wB; auto.
 rewrite Z_mod_mult, Zplus_0_l; apply Zmod_small.
 split; auto with zarith.
 replace wB with (2 * 2 ^ [|digits -1|])%Z; auto.
 apply Zmult_lt_compat_r; auto with zarith.
 case (Zle_lt_or_eq 0 ([|i|] mod 2)); auto with zarith; intros Hi.
 2: generalize H; rewrite <-Hi, Zmult_0_l.
 2: replace 0%Z with [|0|]; auto.
 2: now case eqbP.
 generalize H; replace ([|i|] mod 2) with 1%Z; auto with zarith.
 rewrite Zmult_1_l.
 intros H1.
 assert (H2: [|i << (digits - 1)|] <> [|0|]).
  replace [|0|] with 0%Z; auto with zarith.
 now case eqbP.
Qed.

Lemma bit_split i : ( i = (i >> 1 ) << 1 + bit i 0)%int63.
Proof.
 apply to_Z_inj.
 rewrite -> add_spec, lsl_spec, lsr_spec, bit_0_spec, Zplus_mod_idemp_l.
 replace (2 ^ [|1|]) with 2%Z; auto with zarith.
 rewrite -> Zmult_comm, <-Z_div_mod_eq; auto with zarith.
 rewrite Zmod_small; auto; case (to_Z_bounded i); auto.
Qed.

Lemma bit_lsr x i j :
 (bit (x >> i) j = if j <= i + j then bit x (i + j) else false)%int63.
Proof.
  unfold bit; rewrite lsr_add; case (_ ≤ _); auto.
Qed.

Lemma bit_b2i (b: bool) i : bit b i = (i == 0) && b.
Proof.
 case b; unfold bit; simpl b2i.
 rewrite lsr_1; case (i == 0); auto.
 rewrite lsr0, lsl0, andb_false_r; auto.
Qed.

Lemma bit_1 n : bit 1 n = (n == 0).
Proof.
 unfold bit; rewrite lsr_1.
 case (_ == _); simpl; auto.
Qed.

Local Hint Resolve Z.lt_gt Z.div_pos : zarith.

Lemma to_Z_split x : [|x|] = [|(x  >> 1)|] * 2 + [|bit x 0|].
Proof.
  case (to_Z_bounded x); intros H1x H2x.
  case (to_Z_bounded (bit x 0)); intros H1b H2b.
  assert (F1: 0 <= [|x >> 1|] < wB/2).
    rewrite -> lsr_spec, to_Z_1, Z.pow_1_r. split; auto with zarith.
    apply Zdiv_lt_upper_bound; auto with zarith.
  rewrite -> (bit_split x) at 1.
  rewrite -> add_spec, Zmod_small, lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small;
    split; auto with zarith.
  change wB with ((wB/2)*2); auto with zarith.
  rewrite -> lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small; auto with zarith.
  change wB with ((wB/2)*2); auto with zarith.
  rewrite -> lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small; auto with zarith.
  2: change wB with ((wB/2)*2); auto with zarith.
  change wB with (((wB/2 - 1) * 2 + 1) + 1).
  assert ([|bit x 0|] <= 1); auto with zarith.
  case bit; discriminate.
Qed.

Lemma bit_M i n (H: (digits <= n = true)%int63): bit i n = false.
Proof. unfold bit; rewrite lsr_M_r; auto. Qed.

Lemma bit_half i n (H: (n < digits = true)%int63) : bit (i>>1) n = bit i (n+1).
Proof.
 unfold bit.
 rewrite lsr_add.
 case_eq (n <= (1 + n))%int63.
 replace (1+n)%int63 with (n+1)%int63; [auto|idtac].
 apply to_Z_inj; rewrite !add_spec, Zplus_comm; auto.
 intros H1; assert (H2: n = max_int).
 2: generalize H; rewrite H2; discriminate.
 case (to_Z_bounded n); intros H1n H2n.
 case (Zle_lt_or_eq [|n|] (wB - 1)); auto with zarith;
   intros H2; apply to_Z_inj; auto.
 generalize (add_le_r 1 n); rewrite H1.
 change [|max_int|] with (wB - 1)%Z.
 replace [|1|] with 1%Z; auto with zarith.
Qed.

Lemma bit_ext i j : (forall n, bit i n = bit j n) -> i = j.
Proof.
  case (to_Z_bounded j); case (to_Z_bounded i).
  unfold wB; revert i j; elim size.
    simpl; intros i j ???? _; apply to_Z_inj; lia.
 intros n ih i j.
 rewrite Nat2Z.inj_succ, Z.pow_succ_r by auto with zarith.
 intros hi1 hi2 hj1 hj2 hext.
 rewrite (bit_split i), (bit_split j), hext.
 do 2 f_equal; apply ih; clear ih.
   1, 3: apply to_Z_bounded.
   1, 2: rewrite lsr_spec; auto using Z_lt_div2.
 intros b.
 case (Zle_or_lt [|digits|] [|b|]).
   rewrite <- leb_spec; intros; rewrite !bit_M; auto.
 rewrite <- ltb_spec; intros; rewrite !bit_half; auto.
Qed.

Lemma bit_lsl x i j : bit (x << i) j =
(if (j < i) || (digits <= j) then false else bit x (j - i))%int63.
Proof.
 assert (F1: 1 >= 0) by discriminate.
 case_eq (digits <= j)%int63; intros H.
   rewrite orb_true_r, bit_M; auto.
 set (d := [|digits|]).
 case (Zle_or_lt d [|j|]); intros H1.
   case (leb_spec digits j); rewrite H; auto with zarith.
   intros _ HH; generalize (HH H1); discriminate.
 clear H.
 generalize (ltb_spec j i); case ltb; intros H2; unfold bit; simpl.
   assert (F2: ([|j|] < [|i|])%Z) by (case H2; auto); clear H2.
   replace (is_zero (((x << i) >> j) << (digits - 1))) with true; auto.
   case (to_Z_bounded j); intros  H1j H2j.
   apply sym_equal; rewrite is_zero_spec; apply to_Z_inj.
   rewrite lsl_spec, lsr_spec, lsl_spec.
   replace wB with (2^d); auto.
   pattern d at 1; replace d with ((d - ([|j|] + 1)) + ([|j|] + 1))%Z by ring.
   rewrite Zpower_exp; auto with zarith.
   replace [|i|] with (([|i|] - ([|j|] + 1)) + ([|j|] + 1))%Z by ring.
   rewrite -> Zpower_exp, Zmult_assoc; auto with zarith.
   rewrite Zmult_mod_distr_r.
   rewrite -> Zplus_comm, Zpower_exp, !Zmult_assoc; auto with zarith.
   rewrite -> Z_div_mult_full; auto with zarith.
   rewrite <-Zmult_assoc, <-Zpower_exp; auto with zarith.
   replace (1 + [|digits - 1|])%Z with d; auto with zarith.
   rewrite Z_mod_mult; auto.
 case H2; intros _ H3; case (Zle_or_lt [|i|] [|j|]); intros F2.
   2: generalize (H3 F2); discriminate.
 clear H2 H3.
 apply f_equal with (f := negb).
 apply f_equal with (f := is_zero).
 apply to_Z_inj.
 rewrite -> !lsl_spec, !lsr_spec, !lsl_spec.
 pattern wB at 2 3; replace wB with (2^(1+ [|digits - 1|])); auto.
 rewrite -> Zpower_exp, Z.pow_1_r; auto with zarith.
 rewrite !Zmult_mod_distr_r.
 apply f_equal2 with (f := Zmult); auto.
 replace wB with (2^ d); auto with zarith.
 replace d with ((d - [|i|]) + [|i|])%Z by ring.
 case (to_Z_bounded i); intros  H1i H2i.
 rewrite Zpower_exp; auto with zarith.
 rewrite Zmult_mod_distr_r.
 case (to_Z_bounded j); intros  H1j H2j.
 replace [|j - i|] with ([|j|] - [|i|])%Z.
   2: rewrite sub_spec, Zmod_small; auto with zarith.
 set (d1 := (d - [|i|])%Z).
 set (d2 := ([|j|] - [|i|])%Z).
 pattern [|j|] at 1;
   replace [|j|] with (d2 + [|i|])%Z.
   2: unfold d2; ring.
 rewrite -> Zpower_exp; auto with zarith.
 rewrite -> Zdiv_mult_cancel_r.
   2: generalize (Zpower2_lt_lin [| i |] H1i); auto with zarith.
 rewrite -> (Z_div_mod_eq [|x|] (2^d1)) at 2; auto with zarith.
 pattern d1 at 2;
   replace d1 with (d2 + (1+ (d - [|j|] - 1)))%Z
   by (unfold d1, d2; ring).
 rewrite Zpower_exp; auto with zarith.
 rewrite <-Zmult_assoc, Zmult_comm.
 rewrite Zdiv.Z_div_plus_full_l; auto with zarith.
 rewrite Zpower_exp, Z.pow_1_r; auto with zarith.
 rewrite <-Zplus_mod_idemp_l.
 rewrite <-!Zmult_assoc, Zmult_comm, Z_mod_mult, Zplus_0_l; auto.
Qed.

(* LOR *)
Lemma lor_lsr i1 i2 i: (i1 lor i2) >> i = (i1 >> i) lor (i2 >> i).
Proof.
 apply bit_ext; intros n.
 rewrite -> lor_spec, !bit_lsr, lor_spec.
 case (_ <= _)%int63; auto.
Qed.

Lemma lor_le x y : (y <= x lor y)%int63 = true.
Proof.
 generalize x y (to_Z_bounded x) (to_Z_bounded y); clear x y.
 unfold wB; elim size.
 replace (2^Z_of_nat 0) with 1%Z; auto with zarith.
 intros x y Hx Hy; replace x with 0%int63.
 replace y with 0%int63; auto.
 apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 intros n IH x y; rewrite inj_S.
 unfold Z.succ; rewrite -> Zpower_exp, Z.pow_1_r; auto with zarith.
 intros Hx Hy.
 rewrite leb_spec.
 rewrite -> (to_Z_split y) at 1; rewrite (to_Z_split (x lor y)).
 assert ([|y>>1|] <= [|(x lor y) >> 1|]).
  rewrite -> lor_lsr, <-leb_spec; apply IH.
  rewrite -> lsr_spec, to_Z_1, Z.pow_1_r; split; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  rewrite -> lsr_spec, to_Z_1, Z.pow_1_r; split; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
 assert ([|bit y 0|] <= [|bit (x lor y) 0|]); auto with zarith.
 rewrite lor_spec; do 2 case bit; try discriminate.
Qed.

Lemma bit_0 n : bit 0 n = false.
Proof. unfold bit; rewrite lsr0; auto. Qed.

Lemma bit_add_or x y:
  (forall n, bit x n = true -> bit y n = true -> False) <-> (x + y)%int63= x lor y.
Proof.
 generalize x y (to_Z_bounded x) (to_Z_bounded y); clear x y.
 unfold wB; elim size.
 replace (2^Z_of_nat 0) with 1%Z; auto with zarith.
 intros x y Hx Hy; replace x with 0%int63.
 replace y with 0%int63.
 split; auto; intros _ n; rewrite !bit_0; discriminate.
 apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 intros n IH x y; rewrite inj_S.
 unfold Z.succ; rewrite Zpower_exp, Z.pow_1_r; auto with zarith.
 intros Hx Hy.
 split.
 intros Hn.
 assert (F1: ((x >> 1) + (y >> 1))%int63 = (x >> 1) lor (y >> 1)).
   apply IH.
   rewrite lsr_spec, Z.pow_1_r; split; auto with zarith.
   apply Zdiv_lt_upper_bound; auto with zarith.
   rewrite lsr_spec, Z.pow_1_r; split; auto with zarith.
   apply Zdiv_lt_upper_bound; auto with zarith.
   intros m H1 H2.
   case_eq (digits <= m)%int63;  [idtac | rewrite <- not_true_iff_false];
     intros Heq.
   rewrite bit_M in H1; auto; discriminate.
   rewrite leb_spec in Heq.
   apply (Hn (m + 1)%int63);
     rewrite <-bit_half; auto; rewrite ltb_spec; auto with zarith.
 rewrite (bit_split (x lor y)), lor_lsr, <- F1, lor_spec.
 replace (b2i (bit x 0 || bit y 0)) with (bit x 0 + bit y 0)%int63.
 2: generalize (Hn 0%int63); do 2 case bit; auto; intros [ ]; auto.
 rewrite lsl_add_distr.
 rewrite (bit_split x) at 1; rewrite (bit_split y) at 1.
 rewrite <-!add_assoc; apply f_equal2 with (f := add); auto.
 rewrite add_comm, <-!add_assoc; apply f_equal2 with (f := add); auto.
 rewrite add_comm; auto.
 intros Heq.
 generalize (add_le_r x y); rewrite Heq, lor_le; intro Hb.
 generalize Heq; rewrite (bit_split x) at 1; rewrite (bit_split y )at 1; clear Heq.
 rewrite (fun y => add_comm y (bit x 0)), <-!add_assoc, add_comm,
         <-!add_assoc, (add_comm (bit y 0)), add_assoc, <-lsr_add_distr.
 rewrite (bit_split (x lor y)), lor_spec.
 intros Heq.
 assert (F: (bit x 0 + bit y 0)%int63 = (bit x 0 || bit y 0)).
  assert (F1: (2 | wB)) by (apply Zpower_divide; apply refl_equal).
  assert (F2: 0 < wB) by (apply refl_equal).
  assert (F3: [|bit x  0 + bit y 0|] mod 2 = [|bit x 0 || bit y 0|] mod 2).
  apply trans_equal with (([|(x>>1 + y>>1) << 1|] + [|bit x 0 + bit y 0|]) mod 2).
  rewrite lsl_spec, Zplus_mod, <-Zmod_div_mod; auto with zarith.
  rewrite Z.pow_1_r, Z_mod_mult, Zplus_0_l, Zmod_mod; auto with zarith.
  rewrite (Zmod_div_mod 2 wB), <-add_spec, Heq; auto with zarith.
  rewrite add_spec, <-Zmod_div_mod; auto with zarith.
  rewrite lsl_spec, Zplus_mod, <-Zmod_div_mod; auto with zarith.
  rewrite Z.pow_1_r, Z_mod_mult, Zplus_0_l, Zmod_mod; auto with zarith.
  generalize F3; do 2 case bit; try discriminate; auto.
 case (IH (x >> 1) (y >> 1)).
 rewrite lsr_spec, to_Z_1, Z.pow_1_r; split; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 rewrite lsr_spec, to_Z_1, Z.pow_1_r; split; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 intros _ HH m; case (to_Z_bounded m); intros H1m H2m.
 case_eq (digits <= m)%int63.
 intros Hlm; rewrite bit_M; auto; discriminate.
 rewrite <- not_true_iff_false, leb_spec; intros Hlm.
 case (Zle_lt_or_eq 0 [|m|]); auto; intros Hm.
 replace m with ((m -1) + 1)%int63.
 rewrite <-(bit_half x), <-(bit_half y); auto with zarith.
 apply HH.
 rewrite <-lor_lsr.
 assert (0 <= [|bit (x lor y) 0|] <= 1) by (case bit; split; discriminate).
 rewrite F in Heq; generalize (add_cancel_r _ _ _ Heq).
 intros Heq1; apply to_Z_inj.
 generalize (f_equal to_Z Heq1); rewrite lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small.
 rewrite lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small; auto with zarith.
 case (to_Z_bounded (x lor y)); intros H1xy H2xy.
 rewrite lsr_spec, to_Z_1, Z.pow_1_r; auto with zarith.
 change wB with ((wB/2)*2); split; auto with zarith.
 assert ([|x lor y|] / 2  < wB / 2); auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 split.
 case (to_Z_bounded (x >> 1 + y >> 1)); auto with zarith.
 rewrite add_spec.
 apply Z.le_lt_trans with (([|x >> 1|] + [|y >> 1|]) * 2); auto with zarith.
 case (Zmod_le_first ([|x >> 1|] + [|y >> 1|]) wB); auto with zarith.
 case (to_Z_bounded (x >> 1)); case (to_Z_bounded (y >> 1)); auto with zarith.
 generalize Hb; rewrite (to_Z_split x) at 1; rewrite (to_Z_split y) at 1.
 case (to_Z_bounded (bit x 0)); case (to_Z_bounded (bit y 0)); auto with zarith.
 rewrite ltb_spec, sub_spec, to_Z_1, Zmod_small; auto with zarith.
 rewrite ltb_spec, sub_spec, to_Z_1, Zmod_small; auto with zarith.
 apply to_Z_inj.
 rewrite add_spec, sub_spec, Zplus_mod_idemp_l, to_Z_1, Zmod_small; auto with zarith.
 pose proof (to_Z_inj 0 _ Hm); clear Hm; subst m.
 intros hx hy; revert F; rewrite hx, hy; intros F. generalize (f_equal to_Z F). vm_compute. lia.
Qed.

Lemma addmuldiv_spec x y p :
  [| p |] <= [| digits |] ->
  [| addmuldiv p x y |] = ([| x |] * (2 ^ [| p |]) + [| y |] / (2 ^ ([| digits |] - [| p |]))) mod wB.
Proof.
 intros H.
 assert (Fp := to_Z_bounded p); assert (Fd := to_Z_bounded digits).
 rewrite addmuldiv_def_spec; unfold addmuldiv_def.
 case (bit_add_or (x << p) (y >> (digits - p))); intros HH _.
 rewrite <-HH, add_spec, lsl_spec, lsr_spec, Zplus_mod_idemp_l, sub_spec.
 rewrite (fun x y => Zmod_small (x - y)); auto with zarith.
 intros n; rewrite -> bit_lsl, bit_lsr.
 generalize (add_le_r (digits - p) n).
 case (_ ≤ _); try discriminate.
 rewrite -> sub_spec, Zmod_small; auto with zarith; intros H1.
 case_eq (n < p)%int63; try discriminate.
 rewrite <- not_true_iff_false, ltb_spec; intros H2.
 case (_ ≤ _); try discriminate.
 intros _; rewrite bit_M; try discriminate.
 rewrite -> leb_spec, add_spec, Zmod_small, sub_spec, Zmod_small; auto with zarith.
 rewrite -> sub_spec, Zmod_small; auto with zarith.
Qed.

(* is_even *)
Lemma is_even_bit i : is_even i = negb (bit i 0).
Proof.
 unfold is_even.
 replace (i land 1) with (b2i (bit i 0)).
   case bit; auto.
 apply bit_ext; intros n.
 rewrite bit_b2i, land_spec, bit_1.
 generalize (eqb_spec n 0).
 case (n == 0); auto.
 intros(H,_); rewrite andb_true_r, H; auto.
 rewrite andb_false_r; auto.
Qed.

Lemma is_even_spec x : if is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.
Proof.
rewrite is_even_bit.
generalize (bit_0_spec x); case bit; simpl; auto.
Qed.

Lemma is_even_0 : is_even 0 = true.
Proof. apply refl_equal. Qed.

Lemma is_even_lsl_1 i : is_even (i << 1) = true.
Proof.
 rewrite is_even_bit, bit_lsl; auto.
Qed.

(* Sqrt *)

 (* Direct transcription of an old proof
     of a fortran program in boyer-moore *)

Ltac elim_div :=
  unfold Z.div, Z.modulo;
  match goal with
  |  H : context[ Z.div_eucl ?X ?Y ] |-  _ =>
     generalize dependent H; generalize (Z_div_mod_full X Y) ; case (Z.div_eucl X Y)
  |  |-  context[ Z.div_eucl ?X ?Y ] =>
     generalize (Z_div_mod_full X Y) ; case (Z.div_eucl X Y)
  end; unfold Remainder.

Lemma quotient_by_2 a: a - 1 <= (a/2) + (a/2).
Proof.
 case (Z_mod_lt a 2); auto with zarith.
 intros H1; rewrite Zmod_eq_full; auto with zarith.
Qed.

Lemma sqrt_main_trick j k: 0 <= j -> 0 <= k ->
   (j * k) + j <= ((j + k)/2 + 1)  ^ 2.
Proof.
 intros Hj; generalize Hj k; pattern j; apply natlike_ind;
   auto; clear k j Hj.
 intros _ k Hk; repeat rewrite Zplus_0_l.
 apply  Zmult_le_0_compat; generalize (Z_div_pos k 2); auto with zarith.
 intros j Hj Hrec _ k Hk; pattern k; apply natlike_ind; auto; clear k Hk.
 rewrite -> Zmult_0_r, Zplus_0_r, Zplus_0_l.
 generalize (sqr_pos (Z.succ j / 2)) (quotient_by_2 (Z.succ j));
   unfold Z.succ.
 rewrite Z.pow_2_r, Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
 auto with zarith.
 intros k Hk _.
 replace ((Z.succ j + Z.succ k) / 2) with ((j + k)/2 + 1).
 generalize (Hrec Hj k Hk) (quotient_by_2 (j + k)).
 unfold Z.succ; repeat rewrite Z.pow_2_r;
   repeat rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
 repeat rewrite Zmult_1_l; repeat rewrite Zmult_1_r.
 auto with zarith.
 rewrite -> Zplus_comm, <- Z_div_plus_full_l; auto with zarith.
 apply f_equal2; auto with zarith.
Qed.

Lemma sqrt_main i j: 0 <= i -> 0 < j -> i < ((j + (i/j))/2 + 1) ^ 2.
Proof.
 intros Hi Hj.
 assert (Hij: 0 <= i/j) by (apply Z_div_pos; auto with zarith).
 refine (Z.lt_le_trans _ _ _ _ (sqrt_main_trick _ _ (Zlt_le_weak _ _ Hj) Hij)).
 pattern i at 1; rewrite -> (Z_div_mod_eq i j); case (Z_mod_lt i j); auto with zarith.
Qed.

Lemma sqrt_test_false i j: 0 <= i -> 0 < j -> i/j < j ->  (j + (i/j))/2 < j.
Proof.
  intros Hi Hj; elim_div; intros q r [ ? hr ]; [ lia | subst i ].
  elim_div; intros a b [ h [ hb | ] ]; lia.
Qed.

Lemma sqrt_test_true i j: 0 <= i -> 0 < j -> i/j >= j -> j ^ 2 <= i.
Proof.
 intros Hi Hj Hd; rewrite Z.pow_2_r.
 apply Z.le_trans with (j * (i/j)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
Qed.

Lemma sqrt_step_correct rec i j:
  0 < [|i|] -> 0 < [|j|] -> [|i|] < ([|j|] + 1) ^ 2 ->
   2 * [|j|] < wB ->
  (forall j1 : int,
    0 < [|j1|] < [|j|] -> [|i|] < ([|j1|] + 1) ^ 2 ->
    [|rec i j1|] ^ 2 <= [|i|] < ([|rec i j1|] + 1) ^ 2) ->
  [|sqrt_step rec i j|] ^ 2 <= [|i|] < ([|sqrt_step rec i j|] + 1) ^ 2.
Proof.
 assert (Hp2: 0 < [|2|]) by exact (refl_equal Lt).
 intros Hi Hj Hij H31 Hrec.
 unfold sqrt_step.
 case ltbP; rewrite div_spec.
 - intros hlt.
   assert ([| j + i / j|] = [|j|] + [|i|]/[|j|]) as hj.
     rewrite add_spec, Zmod_small;rewrite div_spec; auto with zarith.
   apply Hrec; rewrite lsr_spec, hj, to_Z_1; change (2 ^ 1) with 2.
   + split; [ | apply sqrt_test_false;auto with zarith].
     replace ([|j|] + [|i|]/[|j|]) with (1 * 2 + (([|j|] - 2) + [|i|] / [|j|])) by ring.
     rewrite Z_div_plus_full_l; auto with zarith.
     assert (0 <= [|i|]/ [|j|]) by (apply Z_div_pos; auto with zarith).
     assert (0 <= ([|j|] - 2 + [|i|] / [|j|]) / 2) ; auto with zarith.
     apply Z.div_pos; [ | lia ].
     case (Zle_lt_or_eq 1 [|j|]); auto with zarith; intros Hj1.
     rewrite <- Hj1, Zdiv_1_r; lia.
   + apply sqrt_main;auto with zarith.
 - split;[apply sqrt_test_true | ];auto with zarith.
Qed.

Lemma iter_sqrt_correct n rec i j: 0 < [|i|] -> 0 < [|j|] ->
  [|i|] < ([|j|] + 1) ^ 2 -> 2 * [|j|] < wB ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      [|i|] < ([|j1|] + 1) ^ 2 -> 2 * [|j1|] < wB ->
       [|rec i j1|] ^ 2 <= [|i|] < ([|rec i j1|] + 1) ^ 2) ->
  [|iter_sqrt n rec i j|] ^ 2 <= [|i|] < ([|iter_sqrt n rec i j|] + 1) ^ 2.
Proof.
 revert rec i j; elim n; unfold iter_sqrt; fold iter_sqrt; clear n.
 intros rec i j Hi Hj Hij H31 Hrec; apply sqrt_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec i j Hi Hj Hij H31 HHrec.
 apply sqrt_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2 Hj31; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite -> inj_S, Z.pow_succ_r.
 apply Z.le_trans with (2 ^Z_of_nat n + [|j2|]); auto with zarith.
 apply Zle_0_nat.
Qed.

Lemma sqrt_init i: 1 < i -> i < (i/2 + 1) ^ 2.
Proof.
 intros Hi.
 assert (H1: 0 <= i - 2) by auto with zarith.
 assert (H2: 1 <= (i / 2) ^ 2); auto with zarith.
   replace i with (1* 2 + (i - 2)); auto with zarith.
   rewrite Z.pow_2_r, Z_div_plus_full_l; auto with zarith.
   generalize (sqr_pos ((i - 2)/ 2)) (Z_div_pos (i - 2) 2).
   rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
   auto with zarith.
 generalize (quotient_by_2 i).
 rewrite -> Z.pow_2_r in H2 |- *;
   repeat (rewrite Zmult_plus_distr_l ||
           rewrite Zmult_plus_distr_r ||
           rewrite Zmult_1_l || rewrite Zmult_1_r).
   auto with zarith.
Qed.

Lemma sqrt_spec : forall x,
       [|sqrt x|] ^ 2 <= [|x|] < ([|sqrt x|] + 1) ^ 2.
Proof.
 intros i; unfold sqrt.
 rewrite compare_spec. case Z.compare_spec; rewrite to_Z_1;
   intros Hi; auto with zarith.
 repeat rewrite Z.pow_2_r; auto with zarith.
 apply iter_sqrt_correct; auto with zarith;
  rewrite lsr_spec, to_Z_1; change (2^1) with 2;  auto with zarith.
  replace [|i|] with (1 * 2 + ([|i|] - 2))%Z; try ring.
  assert (0 <= ([|i|] - 2)/2)%Z by (apply Z_div_pos; auto with zarith).
  rewrite Z_div_plus_full_l; auto with zarith.
  apply sqrt_init; auto.
  assert (W:= Z_mult_div_ge [|i|] 2);assert (W':= to_Z_bounded i);auto with zarith.
  intros j2 H1 H2; contradict H2; apply Zlt_not_le.
  fold wB;assert (W:=to_Z_bounded i).
  apply Z.le_lt_trans with ([|i|]); auto with zarith.
  assert (0 <= [|i|]/2)%Z by (apply Z_div_pos; auto with zarith).
  apply Z.le_trans with (2 * ([|i|]/2)); auto with zarith.
  apply Z_mult_div_ge; auto with zarith.
 case (to_Z_bounded i); repeat rewrite Z.pow_2_r; auto with zarith.
Qed.

(* sqrt2 *)
Lemma sqrt2_step_def rec ih il j:
   sqrt2_step rec ih il j =
   if (ih < j)%int63 then
    let quo := fst (diveucl_21 ih il j) in
    if (quo < j)%int63 then
     let m :=
      match j +c quo with
      | C0 m1 => m1 >> 1
      | C1 m1 => (m1 >> 1 + 1 << (digits -1))%int63
      end in
     rec ih il m
    else j
   else j.
Proof.
 unfold sqrt2_step; case diveucl_21; intros;simpl.
 case (j +c i);trivial.
Qed.

Lemma sqrt2_lower_bound ih il j:
   [|| WW ih il||]  < ([|j|] + 1) ^ 2 -> [|ih|] <= [|j|].
Proof.
 intros H1.
 case (to_Z_bounded j); intros Hbj _.
 case (to_Z_bounded il); intros Hbil _.
 case (to_Z_bounded ih); intros Hbih Hbih1.
 assert (([|ih|] < [|j|] + 1)%Z); auto with zarith.
 apply Zlt_square_simpl; auto with zarith.
 simpl zn2z_to_Z in H1.
 repeat rewrite <-Z.pow_2_r.
 refine (Z.le_lt_trans _ _ _ _ H1).
 apply Z.le_trans with ([|ih|] * wB)%Z;try rewrite Z.pow_2_r; auto with zarith.
Qed.

Lemma diveucl_21_spec_aux : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := diveucl_21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
Proof.
 intros a1 a2 b H1 H2;assert (W:= diveucl_21_spec a1 a2 b).
 assert (W1:= to_Z_bounded a1).
 assert (W2:= to_Z_bounded a2).
 assert (Wb:= to_Z_bounded b).
 assert ([|b|]>0) by (auto with zarith).
 generalize (Z_div_mod ([|a1|]*wB+[|a2|]) [|b|] H).
 revert W.
 destruct (diveucl_21 a1 a2 b); destruct (Z.div_eucl ([|a1|]*wB+[|a2|]) [|b|]).
 intros (H', H''); rewrite H', H''; clear H' H''.
 intros (H', H''); split; [ |exact H''].
 rewrite H', Zmult_comm, Z.mod_small; [reflexivity| ].
 split.
 { revert H'; case z; [now simpl..|intros p H'].
   exfalso; apply (Z.lt_irrefl 0), (Z.le_lt_trans _ ([|a1|] * wB + [|a2|])).
   { now apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg| ]. }
   rewrite H'; apply (Zplus_lt_reg_r _ _ (- z0)); ring_simplify.
   apply (Z.le_lt_trans _ (- [|b|])); [ |now auto with zarith].
   rewrite Z.opp_eq_mul_m1; apply Zmult_le_compat_l; [ |now apply Wb].
   rewrite <-!Pos2Z.opp_pos, <-Z.opp_le_mono.
   now change 1 with (Z.succ 0); apply Zlt_le_succ. }
 rewrite <-Z.nle_gt; intro Hz; revert H2; apply Zle_not_lt.
 rewrite (Z.div_unique_pos (wB * [|a1|] + [|a2|]) wB [|a1|] [|a2|]);
   [ |now simpl..].
 rewrite Z.mul_comm, H'.
 rewrite (Z.div_unique_pos (wB * [|b|] + z0) wB [|b|] z0) at 1;
   [ |split; [ |apply (Z.lt_trans _ [|b|])]; now simpl|reflexivity].
 apply Z_div_le; [now simpl| ]; rewrite Z.mul_comm; apply Zplus_le_compat_r.
 now apply Zmult_le_compat_l.
Qed.

Lemma div2_phi ih il j: (2^62 <= [|j|] -> [|ih|] < [|j|] ->
  [|fst (diveucl_21 ih il j)|] = [|| WW ih il||] /[|j|])%Z.
Proof.
 intros Hj Hj1.
 generalize (diveucl_21_spec_aux ih il j Hj Hj1).
 case diveucl_21; intros q r (Hq, Hr).
 apply Zdiv_unique with [|r|]; auto with zarith.
 simpl @fst; apply eq_trans with (1 := Hq); ring.
Qed.

Lemma sqrt2_step_correct rec ih il j:
  2 ^ (Z_of_nat (size - 2)) <= [|ih|] ->
  0 < [|j|] -> [|| WW ih il||] < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] < [|j|] ->  [|| WW ih il||] < ([|j1|] + 1) ^ 2 ->
     [|rec ih il j1|] ^ 2 <= [||WW ih il||] < ([|rec ih il j1|] + 1) ^ 2) ->
  [|sqrt2_step rec ih il j|] ^ 2 <= [||WW ih il ||]
      < ([|sqrt2_step rec ih il j|] + 1) ^  2.
Proof.
 assert (Hp2: (0 < [|2|])%Z) by exact (refl_equal Lt).
 intros Hih Hj Hij Hrec; rewrite sqrt2_step_def.
 assert (H1: ([|ih|] <= [|j|])%Z) by (apply sqrt2_lower_bound with il; auto).
 case (to_Z_bounded ih); intros Hih1 _.
 case (to_Z_bounded il); intros Hil1 _.
 case (to_Z_bounded j); intros _ Hj1.
 assert (Hp3: (0 < [||WW ih il||])).
 {simpl zn2z_to_Z;apply Z.lt_le_trans with ([|ih|] * wB)%Z; auto with zarith.
  apply Zmult_lt_0_compat; auto with zarith.
  refine (Z.lt_le_trans _ _ _ _ Hih); auto with zarith. }
 cbv zeta.
 case_eq (ih < j)%int63;intros Heq.
 rewrite -> ltb_spec in Heq.
 2: rewrite <-not_true_iff_false, ltb_spec in Heq.
 2: split; auto.
 2: apply sqrt_test_true; auto with zarith.
 2: unfold zn2z_to_Z; replace [|ih|] with [|j|]; auto with zarith.
 2: assert (0 <= [|il|]/[|j|]) by (apply Z_div_pos; auto with zarith).
 2: rewrite Zmult_comm, Z_div_plus_full_l; unfold base; auto with zarith.
 case (Zle_or_lt (2^(Z_of_nat size -1)) [|j|]); intros Hjj.
 case_eq (fst (diveucl_21 ih il j) < j)%int63;intros Heq0.
 2: rewrite <-not_true_iff_false, ltb_spec, (div2_phi _ _ _ Hjj Heq) in Heq0.
 2: split; auto; apply sqrt_test_true; auto with zarith.
 rewrite -> ltb_spec, (div2_phi _ _ _ Hjj Heq) in Heq0.
 match goal with |- context[rec _ _ ?X] =>
  set (u := X)
 end.
 assert (H: [|u|] = ([|j|] + ([||WW ih il||])/([|j|]))/2).
 { unfold u; generalize (addc_spec j (fst (diveucl_21 ih il j)));
  case addc;unfold interp_carry;rewrite (div2_phi _ _ _ Hjj Heq);simpl zn2z_to_Z.
  { intros i H;rewrite lsr_spec, H;trivial. }
  intros i H;rewrite <- H.
  case (to_Z_bounded i); intros H1i H2i.
  rewrite -> add_spec, Zmod_small, lsr_spec.
  { change (1 * wB) with ([|(1 << (digits -1))|] * 2)%Z.
    rewrite Z_div_plus_full_l; auto with zarith. }
  change wB with (2 * (wB/2))%Z; auto.
  replace [|(1 << (digits - 1))|] with (wB/2); auto.
  rewrite lsr_spec; auto.
  replace (2^[|1|]) with 2%Z; auto.
  split; auto with zarith.
  assert ([|i|]/2 < wB/2); auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith. }
 apply Hrec; rewrite H; clear u H.
 assert (Hf1: 0 <= [||WW ih il||]/ [|j|]) by (apply Z_div_pos; auto with zarith).
 case (Zle_lt_or_eq 1 ([|j|])); auto with zarith; intros Hf2.
 2: contradict Heq0; apply Zle_not_lt; rewrite <- Hf2, Zdiv_1_r; auto with zarith.
 split.
 replace ([|j|] + [||WW ih il||]/ [|j|])%Z with
        (1 * 2 + (([|j|] - 2) + [||WW ih il||] / [|j|])) by lia.
 rewrite Z_div_plus_full_l; auto with zarith.
 assert (0 <= ([|j|] - 2 + [||WW ih il||] / [|j|]) / 2) ; auto with zarith.
 apply sqrt_test_false; auto with zarith.
 apply sqrt_main; auto with zarith.
 contradict Hij; apply Zle_not_lt.
 assert ((1 + [|j|]) <= 2 ^ (Z_of_nat size - 1)); auto with zarith.
 apply Z.le_trans with ((2 ^ (Z_of_nat size - 1)) ^2); auto with zarith.
 assert (0 <= 1 + [|j|]); auto with zarith.
 apply Zmult_le_compat; auto with zarith.
 change ((2 ^ (Z_of_nat size - 1))^2) with (2 ^ (Z_of_nat size - 2) * wB).
 apply Z.le_trans with ([|ih|] * wB); auto with zarith.
 unfold zn2z_to_Z, wB; auto with zarith.
Qed.

Lemma iter2_sqrt_correct n rec ih il j:
  2^(Z_of_nat (size - 2)) <= [|ih|] ->  0 < [|j|] -> [||WW ih il||] < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      [||WW ih il||] < ([|j1|] + 1) ^ 2 ->
       [|rec ih il j1|] ^ 2 <= [||WW ih il||] < ([|rec ih il j1|] + 1) ^ 2)  ->
  [|iter2_sqrt n rec ih il j|] ^ 2 <= [||WW ih il||]
      < ([|iter2_sqrt n rec ih il j|] + 1) ^ 2.
Proof.
 revert rec ih il j; elim n; unfold iter2_sqrt; fold iter2_sqrt; clear n.
 intros rec ih il j Hi Hj Hij Hrec; apply sqrt2_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec ih il j Hi Hj Hij HHrec.
 apply sqrt2_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite -> inj_S, Z.pow_succ_r.
 apply Z.le_trans with (2 ^Z_of_nat n + [|j2|])%Z; auto with zarith.
 apply Zle_0_nat.
Qed.

Lemma sqrt2_spec : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
 Proof.
 intros ih il Hih; unfold sqrt2.
 change [||WW ih il||] with ([||WW ih il||]).
 assert (Hbin: forall s, s * s + 2* s + 1 = (s + 1) ^ 2) by
  (intros s; ring).
 assert (Hb: 0 <= wB) by (red; intros HH; discriminate).
 assert (Hi2: [||WW ih il ||] < ([|max_int|] + 1) ^ 2).
  apply Z.le_lt_trans with ((wB - 1) * wB + (wB - 1)); auto with zarith.
  2: apply refl_equal.
  case (to_Z_bounded ih); case (to_Z_bounded il); intros H1 H2 H3 H4.
  unfold zn2z_to_Z; auto with zarith.
 case (iter2_sqrt_correct size (fun _ _ j => j) ih il max_int); auto with zarith.
 apply refl_equal.
 intros j1 _ HH; contradict HH.
 apply Zlt_not_le.
 case (to_Z_bounded j1); auto with zarith.
 change (2 ^ Z_of_nat size) with ([|max_int|]+1)%Z; auto with zarith.
 set (s := iter2_sqrt size (fun _ _ j : int=> j) ih il max_int).
 intros Hs1 Hs2.
 generalize (mulc_spec s s); case mulc.
 simpl fst; simpl snd; intros ih1 il1 Hihl1.
 generalize (subc_spec il il1).
 case subc; intros il2 Hil2.
 simpl interp_carry in Hil2.
 case_eq (ih1  < ih)%int63;  [idtac | rewrite <- not_true_iff_false];
  rewrite ltb_spec; intros Heq.
 unfold interp_carry; rewrite Zmult_1_l.
 rewrite -> Z.pow_2_r, Hihl1, Hil2.
 case (Zle_lt_or_eq ([|ih1|] + 1) ([|ih|])); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with ([||WW ih1 il1||] + 2 * [|s|] + 1).
 unfold zn2z_to_Z.
 case (to_Z_bounded il); intros Hpil _.
 assert (Hl1l: [|il1|] <= [|il|]).
  case (to_Z_bounded il2); rewrite Hil2; auto with zarith.
 assert ([|ih1|] * wB + 2 * [|s|] + 1 <= [|ih|] * wB); auto with zarith.
 case (to_Z_bounded s); intros _ Hps.
 case (to_Z_bounded ih1); intros Hpih1 _; auto with zarith.
 apply Z.le_trans with (([|ih1|] + 2) * wB); auto with zarith.
 rewrite Zmult_plus_distr_l.
 assert (2 * [|s|] + 1 <= 2 * wB); auto with zarith.
 unfold zn2z_to_Z; rewrite <-Hihl1, Hbin; auto.
 intros H2; split.
 unfold zn2z_to_Z; rewrite <- H2; ring.
 replace (wB + ([|il|] - [|il1|])) with ([||WW ih il||] - ([|s|] * [|s|])).
 rewrite <-Hbin in Hs2; auto with zarith.
 rewrite Hihl1; unfold zn2z_to_Z; rewrite <- H2; ring.
 unfold interp_carry.
 case (Zle_lt_or_eq [|ih|] [|ih1|]); auto with zarith; intros H.
 contradict Hs1.
 apply Zlt_not_le; rewrite Z.pow_2_r, Hihl1.
 unfold zn2z_to_Z.
 case (to_Z_bounded il); intros _ H2.
 apply Z.lt_le_trans with (([|ih|] + 1) * wB + 0).
 rewrite Zmult_plus_distr_l, Zplus_0_r; auto with zarith.
 case (to_Z_bounded il1); intros H3 _.
 apply Zplus_le_compat; auto with zarith.
 split.
 rewrite Z.pow_2_r, Hihl1.
 unfold zn2z_to_Z; ring[Hil2 H].
 replace [|il2|] with ([||WW ih il||] - [||WW ih1 il1||]).
 unfold zn2z_to_Z at 2; rewrite <-Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold zn2z_to_Z; rewrite H, Hil2; ring.
 unfold interp_carry in Hil2 |- *.
 assert (Hsih: [|ih - 1|] = [|ih|] - 1).
  rewrite sub_spec, Zmod_small; auto; replace [|1|] with 1; auto.
  case (to_Z_bounded ih); intros H1 H2.
  split; auto with zarith.
  apply Z.le_trans with (wB/4 - 1); auto with zarith.
 case_eq (ih1 < ih - 1)%int63;  [idtac | rewrite <- not_true_iff_false];
  rewrite ltb_spec, Hsih; intros Heq.
 rewrite Z.pow_2_r, Hihl1.
 case (Zle_lt_or_eq ([|ih1|] + 2) [|ih|]); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with ([||WW ih1 il1||] + 2 * [|s|] + 1).
 unfold zn2z_to_Z.
 assert ([|ih1|] * wB + 2 * [|s|] + 1 <= [|ih|] * wB + ([|il|] - [|il1|]));
  auto with zarith.
 rewrite <-Hil2.
 case (to_Z_bounded il2); intros Hpil2 _.
 apply Z.le_trans with ([|ih|] * wB + - wB); auto with zarith.
 case (to_Z_bounded s);  intros _ Hps.
 assert (2 * [|s|] + 1 <= 2 * wB); auto with zarith.
 apply Z.le_trans with ([|ih1|] * wB + 2 * wB); auto with zarith.
 assert (Hi: ([|ih1|] + 3) * wB <= [|ih|] * wB); auto with zarith.
 rewrite Zmult_plus_distr_l in Hi; auto with zarith.
 unfold zn2z_to_Z; rewrite <-Hihl1, Hbin; auto.
 intros H2; unfold zn2z_to_Z; rewrite <-H2.
 split.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2; ring.
 replace (1 * wB + [|il2|]) with ([||WW ih il||] - [||WW ih1 il1||]).
 unfold zn2z_to_Z at 2; rewrite <-Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold zn2z_to_Z; rewrite <-H2.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2; ring.
 case (Zle_lt_or_eq ([|ih|] - 1) ([|ih1|])); auto with zarith; intros H1.
 assert (He: [|ih|] = [|ih1|]).
   apply Zle_antisym; auto with zarith.
   case (Zle_or_lt [|ih1|] [|ih|]); auto; intros H2.
   contradict Hs1; apply Zlt_not_le; rewrite Z.pow_2_r, Hihl1.
  unfold zn2z_to_Z.
  case (to_Z_bounded il); intros _ Hpil1.
  apply Z.lt_le_trans with (([|ih|] + 1) * wB).
  rewrite Zmult_plus_distr_l, Zmult_1_l; auto with zarith.
  case (to_Z_bounded il1); intros Hpil2 _.
  apply Z.le_trans with (([|ih1|]) * wB); auto with zarith.
 contradict Hs1; apply Zlt_not_le; rewrite Z.pow_2_r, Hihl1.
 unfold zn2z_to_Z; rewrite He.
 assert ([|il|] - [|il1|] < 0); auto with zarith.
 rewrite <-Hil2.
 case (to_Z_bounded il2); auto with zarith.
 split.
 rewrite Z.pow_2_r, Hihl1.
 unfold zn2z_to_Z; rewrite <-H1.
 apply trans_equal with ([|ih|] * wB + [|il1|] + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2; ring.
 replace [|il2|] with ([||WW ih il||] - [||WW ih1 il1||]).
 unfold zn2z_to_Z at 2; rewrite <- Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold zn2z_to_Z.
 rewrite <-H1.
 ring_simplify.
 apply trans_equal with (wB + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2; ring.
Qed.

(* of_pos *)
Lemma of_pos_rec_spec (k: nat) :
  (k <= size)%nat →
  ∀ p, φ(of_pos_rec k p) = Zpos p mod 2 ^ Z.of_nat k.
Proof.
  elim k; clear k.
    intros _ p; simpl; rewrite to_Z_0, Zmod_1_r; reflexivity.
  intros n ih hn.
  assert (n <= size)%nat as hn' by lia.
  specialize (ih hn').
  intros [ p | p | ].
  3: {
    rewrite Zmod_small. reflexivity.
    split. lia.
    apply Zpower_gt_1; lia.
  }
  - simpl.
    destruct (bit_add_or (of_pos_rec n p << 1) 1) as (H1, _).
    rewrite <- H1;clear H1.
    2: {
      intros i; rewrite bit_lsl, bit_1.
      case eqbP.
      + intros h; apply to_Z_inj in h; subst. exact (λ e _, diff_false_true e).
      + exact (λ _ _, diff_false_true).
    }
    rewrite add_spec, lsl_spec, ih, to_Z_1; clear ih.
    rewrite Z.pow_pos_fold, Zpos_P_of_succ_nat.
    change (Zpos p~1) with (2 ^ 1 * Zpos p + 1)%Z.
    rewrite Zmod_distr by lia.
    rewrite Zpower_Zsucc by auto with zarith.
    rewrite Zplus_mod_idemp_l.
    rewrite Zmod_small.
      rewrite Zmult_mod_distr_l; lia.
    set (a := Z.of_nat n).
    set (b := Zpos p).
    change (2 ^ 1) with 2.
    pose proof (pow2_pos a (Nat2Z.is_nonneg _)).
    elim_div; intros x y [ ? ha]. lia.
    destruct ha as [ ha | ]. 2: lia.
    split. lia.
    apply Z.lt_le_trans with (2 ^ (a + 1)).
    2: apply Z.pow_le_mono_r; subst a; lia.
    fold (Z.succ a); rewrite Z.pow_succ_r. lia.
    subst a; lia.
  - simpl. rewrite lsl_spec, ih, to_Z_1, Zmod_small.
      rewrite Z.pow_pos_fold, Zpos_P_of_succ_nat, Zpower_Zsucc by lia.
      change (Zpos p~0) with (2 ^ 1 * Zpos p)%Z.
      rewrite Z.mul_mod_distr_l; auto with zarith.
    set (a := Z.of_nat n).
    set (b := Zpos p).
    change (2 ^ 1) with 2.
    pose proof (pow2_pos a (Nat2Z.is_nonneg _)).
    elim_div; intros x y [ ? ha]. lia.
    destruct ha as [ ha | ]. 2: lia.
    split. lia.
    apply Z.lt_le_trans with (2 ^ (a + 1)).
    2: apply Z.pow_le_mono_r; subst a; lia.
    fold (Z.succ a); rewrite Z.pow_succ_r. lia.
    subst a; lia.
Qed.

Lemma is_int n :
  0 <= n < 2 ^ φ digits →
  n = φ (of_Z n).
Proof.
  destruct n. reflexivity. 2: lia.
  intros [_ h]. simpl.
  unfold of_pos. rewrite of_pos_rec_spec by lia.
  symmetry; apply Z.mod_small. split. lia. exact h.
Qed.

Lemma of_Z_spec n : [| of_Z n |] = n mod wB.
Proof.
  destruct n. reflexivity.
  { now simpl; unfold of_pos; rewrite of_pos_rec_spec by lia. }
  simpl; unfold of_pos; rewrite opp_spec.
  rewrite of_pos_rec_spec; [ |auto]; fold wB.
  now rewrite <-(Z.sub_0_l), Zminus_mod_idemp_r.
Qed.

(* General lemmas *)
Lemma negbE a b : a = negb b → negb a = b.
Proof. intros ->; apply negb_involutive. Qed.

Lemma Z_oddE a : Z.odd a = (a mod 2 =? 1)%Z.
Proof. rewrite Zmod_odd; case Z.odd; reflexivity. Qed.

Lemma Z_evenE a : Z.even a = (a mod 2 =? 0)%Z.
Proof. rewrite Zmod_even; case Z.even; reflexivity. Qed.

(* is_zero *)
Lemma is_zeroE n : is_zero n = Z.eqb (φ n) 0.
Proof.
  case Z.eqb_spec.
  - intros h; apply (to_Z_inj n 0) in h; subst n; reflexivity.
  - generalize (proj1 (is_zero_spec n)).
    case is_zero; auto; intros ->; auto; destruct 1; reflexivity.
Qed.

(* bit *)
Lemma bitE i j : bit i j = Z.testbit φ(i) φ(j).
Proof.
  apply negbE; rewrite is_zeroE, lsl_spec, lsr_spec.
  generalize (φ i) (to_Z_bounded i) (φ j) (to_Z_bounded j); clear i j;
  intros i [hi hi'] j [hj hj'].
  rewrite Z.testbit_eqb by auto; rewrite <- Z_oddE, Z.negb_odd, Z_evenE.
  remember (i / 2 ^ j) as k.
  change wB with (2 * 2 ^ φ (digits - 1)).
  unfold Z.modulo at 2.
  generalize (Z_div_mod_full k 2 (λ k, let 'eq_refl := k in I)); unfold Remainder.
  destruct Z.div_eucl as [ p q ]; intros [hk [ hq | ]]. 2: lia.
  rewrite hk.
  remember φ (digits - 1) as m.
  replace ((_ + _) * _) with (q * 2 ^ m + p * (2 * 2 ^ m)) by ring.
  rewrite Z_mod_plus by (subst m; reflexivity).
  assert (q = 0 ∨ q = 1) as D by lia.
  destruct D; subst; reflexivity.
Qed.

(* land, lor, lxor *)
Lemma lt_pow_lt_log d k n :
  0 < d <= n →
  0 <= k < 2 ^ d →
  Z.log2 k < n.
Proof.
  intros [hd hdn] [hk hkd].
  assert (k = 0 ∨ 0 < k) as D by lia.
  clear hk; destruct D as [ hk | hk ].
  - subst k; simpl; lia.
  - apply Z.log2_lt_pow2. lia.
    eapply Z.lt_le_trans. eassumption.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_spec' x y : φ (x land y) = Z.land φ(x) φ(y).
Proof.
  apply Z.bits_inj'; intros n hn.
  destruct (to_Z_bounded (x land y)) as [ hxy hxy' ].
  destruct (to_Z_bounded x) as [ hx hx' ].
  destruct (to_Z_bounded y) as [ hy hy' ].
  case (Z_lt_le_dec n (φ digits)); intros hd.
  2: {
    rewrite !Z.bits_above_log2; auto.
    - apply Z.land_nonneg; auto.
    - eapply Z.le_lt_trans.
        apply Z.log2_land; assumption.
       apply Z.min_lt_iff.
       left. apply (lt_pow_lt_log φ digits). exact (conj eq_refl hd).
      split; assumption.
    - apply (lt_pow_lt_log φ digits). exact (conj eq_refl hd).
      split; assumption.
  }
  rewrite (is_int n).
    rewrite Z.land_spec, <- !bitE, land_spec; reflexivity.
  apply (conj hn).
  apply (Z.lt_trans _ _ _ hd).
  apply Zpower2_lt_lin. lia.
Qed.

Lemma lor_spec' x y : φ (x lor y) = Z.lor φ(x) φ(y).
Proof.
  apply Z.bits_inj'; intros n hn.
  destruct (to_Z_bounded (x lor y)) as [ hxy hxy' ].
  destruct (to_Z_bounded x) as [ hx hx' ].
  destruct (to_Z_bounded y) as [ hy hy' ].
  case (Z_lt_le_dec n (φ digits)); intros hd.
  2: {
    rewrite !Z.bits_above_log2; auto.
    - apply Z.lor_nonneg; auto.
    - rewrite Z.log2_lor by assumption.
      apply Z.max_lub_lt; apply (lt_pow_lt_log φ digits); split; assumption || reflexivity.
    - apply (lt_pow_lt_log φ digits); split; assumption || reflexivity.
  }
  rewrite (is_int n).
    rewrite Z.lor_spec, <- !bitE, lor_spec; reflexivity.
  apply (conj hn).
  apply (Z.lt_trans _ _ _ hd).
  apply Zpower2_lt_lin. lia.
Qed.

Lemma lxor_spec' x y : φ (x lxor y) = Z.lxor φ(x) φ(y).
Proof.
  apply Z.bits_inj'; intros n hn.
  destruct (to_Z_bounded (x lxor y)) as [ hxy hxy' ].
  destruct (to_Z_bounded x) as [ hx hx' ].
  destruct (to_Z_bounded y) as [ hy hy' ].
  case (Z_lt_le_dec n (φ digits)); intros hd.
  2: {
    rewrite !Z.bits_above_log2; auto.
    - apply Z.lxor_nonneg; split; auto.
    - eapply Z.le_lt_trans.
        apply Z.log2_lxor; assumption.
      apply Z.max_lub_lt; apply (lt_pow_lt_log φ digits); split; assumption || reflexivity.
    - apply (lt_pow_lt_log φ digits); split; assumption || reflexivity.
  }
  rewrite (is_int n).
    rewrite Z.lxor_spec, <- !bitE, lxor_spec; reflexivity.
  apply (conj hn).
  apply (Z.lt_trans _ _ _ hd).
  apply Zpower2_lt_lin. lia.
Qed.

Lemma landC i j : i land j = j land i.
Proof.
 apply bit_ext; intros n.
 rewrite !land_spec, andb_comm; auto.
Qed.

Lemma landA i j k : i land (j land k) = i land j land k.
Proof.
 apply bit_ext; intros n.
 rewrite !land_spec, andb_assoc; auto.
Qed.

Lemma land0 i : 0 land i = 0%int63.
Proof.
 apply bit_ext; intros n.
 rewrite land_spec, bit_0; auto.
Qed.

Lemma land0_r i : i land 0 = 0%int63.
Proof. rewrite landC; exact (land0 i). Qed.

Lemma lorC i j : i lor j = j lor i.
Proof.
 apply bit_ext; intros n.
 rewrite !lor_spec, orb_comm; auto.
Qed.

Lemma lorA i j k : i lor (j lor k) = i lor j lor k.
Proof.
 apply bit_ext; intros n.
 rewrite !lor_spec, orb_assoc; auto.
Qed.

Lemma lor0 i : 0 lor i = i.
Proof.
 apply bit_ext; intros n.
 rewrite lor_spec, bit_0; auto.
Qed.

Lemma lor0_r i : i lor 0 = i.
Proof. rewrite lorC; exact (lor0 i). Qed.

Lemma lxorC i j : i lxor j = j lxor i.
Proof.
 apply bit_ext; intros n.
 rewrite !lxor_spec, xorb_comm; auto.
Qed.

Lemma lxorA i j k : i lxor (j lxor k) = i lxor j lxor k.
Proof.
 apply bit_ext; intros n.
 rewrite !lxor_spec, xorb_assoc; auto.
Qed.

Lemma lxor0 i : 0 lxor i = i.
Proof.
 apply bit_ext; intros n.
 rewrite lxor_spec, bit_0, xorb_false_l; auto.
Qed.

Lemma lxor0_r i : i lxor 0 = i.
Proof. rewrite lxorC; exact (lxor0 i). Qed.
