(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import NAxioms NSub NDiv NGcd.

(** * Least Common Multiple *)

(** Unlike other functions around, we will define lcm below instead of
  axiomatizing it. Indeed, there is no "prior art" about lcm in the
  standard library to be compliant with, and the generic definition
  of lcm via gcd is quite reasonable.

  By the way, we also state here some combined properties of div/mod
  and gcd.
*)

Module Type NLcmProp
 (Import A : NAxiomsSig')
 (Import B : NSubProp A)
 (Import C : NDivProp A B)
 (Import D : NGcdProp A B).

(** Divibility and modulo *)

Lemma mod_divide : forall a b, b~=0 -> (a mod b == 0 <-> (b|a)).
Proof.
 intros a b Hb. split.
 intros Hab. exists (a/b). rewrite mul_comm.
  rewrite (div_mod a b Hb) at 1. rewrite Hab; now nzsimpl.
 intros (c,Hc). rewrite Hc. now apply mod_mul.
Qed.

Lemma divide_div_mul_exact : forall a b c, b~=0 -> (b|a) ->
 (c*a)/b == c*(a/b).
Proof.
 intros a b c Hb H.
 apply mul_cancel_l with b; trivial.
 rewrite mul_assoc, mul_shuffle0.
 assert (H':=H). apply mod_divide, div_exact in H'; trivial.
 rewrite <- H', (mul_comm a c).
 symmetry. apply div_exact; trivial.
 apply mod_divide; trivial.
 now apply divide_mul_r.
Qed.

(** Gcd of divided elements, for exact divisions *)

Lemma gcd_div_factor : forall a b c, c~=0 -> (c|a) -> (c|b) ->
 gcd (a/c) (b/c) == (gcd a b)/c.
Proof.
 intros a b c Hc Ha Hb.
 apply mul_cancel_l with c; try order.
 assert (H:=gcd_greatest _ _ _ Ha Hb).
 apply mod_divide, div_exact in H; try order.
 rewrite <- H.
 rewrite <- gcd_mul_mono_l; try order.
 f_equiv; symmetry; apply div_exact; try order;
  apply mod_divide; trivial; try order.
Qed.

Lemma gcd_div_gcd : forall a b g, g~=0 -> g == gcd a b ->
 gcd (a/g) (b/g) == 1.
Proof.
 intros a b g NZ EQ. rewrite gcd_div_factor.
 now rewrite <- EQ, div_same.
 generalize (gcd_nonneg a b); order.
 rewrite EQ; apply gcd_divide_l.
 rewrite EQ; apply gcd_divide_r.
Qed.

(** The following equality is crucial for Euclid algorithm *)

Lemma gcd_mod : forall a b, b~=0 -> gcd (a mod b) b == gcd b a.
Proof.
 intros a b Hb. rewrite (gcd_comm _ b).
 rewrite <- (gcd_add_mult_diag_r b (a mod b) (a/b)).
 now rewrite add_comm, mul_comm, <- div_mod.
Qed.

(** We now define lcm thanks to gcd:

    lcm a b = a * (b / gcd a b)
            = (a / gcd a b) * b
            = (a*b) / gcd a b

   Nota: [lcm 0 0] should be 0, which isn't garantee with the third
   equation above.
*)

Definition lcm a b := a*(b/gcd a b).

Instance lcm_wd : Proper (eq==>eq==>eq) lcm.
Proof. unfold lcm. solve_proper. Qed.

Lemma lcm_equiv1 : forall a b, gcd a b ~= 0 ->
  a * (b / gcd a b) == (a*b)/gcd a b.
Proof.
 intros a b H. rewrite divide_div_mul_exact; try easy. apply gcd_divide_r.
Qed.

Lemma lcm_equiv2 : forall a b, gcd a b ~= 0 ->
  (a / gcd a b) * b == (a*b)/gcd a b.
Proof.
 intros a b H. rewrite 2 (mul_comm _ b).
 rewrite divide_div_mul_exact; try easy. apply gcd_divide_l.
Qed.

Lemma gcd_div_swap : forall a b,
 (a / gcd a b) * b == a * (b / gcd a b).
Proof.
 intros a b. destruct (eq_decidable (gcd a b) 0) as [EQ|NEQ].
 apply gcd_eq_0 in EQ. destruct EQ as (EQ,EQ'). rewrite EQ, EQ'. now nzsimpl.
 now rewrite lcm_equiv1, <-lcm_equiv2.
Qed.

Lemma divide_lcm_l : forall a b, (a | lcm a b).
Proof.
 unfold lcm. intros a b. apply divide_factor_l.
Qed.

Lemma divide_lcm_r : forall a b, (b | lcm a b).
Proof.
 unfold lcm. intros a b. rewrite <- gcd_div_swap.
 apply divide_factor_r.
Qed.

Lemma divide_div : forall a b c, a~=0 -> (a|b) -> (b|c) -> (b/a|c/a).
Proof.
 intros a b c Ha Hb (c',Hc). exists c'.
 now rewrite <- divide_div_mul_exact, Hc.
Qed.

Lemma lcm_least : forall a b c,
 (a | c) -> (b | c) -> (lcm a b | c).
Proof.
 intros a b c Ha Hb. unfold lcm.
 destruct (eq_decidable (gcd a b) 0) as [EQ|NEQ].
 apply gcd_eq_0 in EQ. destruct EQ as (EQ,EQ'). rewrite EQ in *. now nzsimpl.
 assert (Ga := gcd_divide_l a b).
 assert (Gb := gcd_divide_r a b).
 set (g:=gcd a b) in *.
 assert (Ha' := divide_div g a c NEQ Ga Ha).
 assert (Hb' := divide_div g b c NEQ Gb Hb).
 destruct Ha' as (a',Ha'). rewrite Ha', mul_comm in Hb'.
 apply gauss in Hb'; [|apply gcd_div_gcd; unfold g; trivial using gcd_comm].
 destruct Hb' as (b',Hb').
 exists b'.
 rewrite mul_shuffle3, <- Hb'.
 rewrite (proj2 (div_exact c g NEQ)).
 rewrite Ha', mul_shuffle3, (mul_comm a a'). f_equiv.
 symmetry. apply div_exact; trivial.
 apply mod_divide; trivial.
 apply mod_divide; trivial. transitivity a; trivial.
Qed.

Lemma lcm_comm : forall a b, lcm a b == lcm b a.
Proof.
 intros a b. unfold lcm. rewrite (gcd_comm b), (mul_comm b).
 now rewrite <- gcd_div_swap.
Qed.

Lemma lcm_divide_iff : forall n m p,
  (lcm n m | p) <-> (n | p) /\ (m | p).
Proof.
 intros. split. split.
 transitivity (lcm n m); trivial using divide_lcm_l.
 transitivity (lcm n m); trivial using divide_lcm_r.
 intros (H,H'). now apply lcm_least.
Qed.

Lemma lcm_unique : forall n m p,
 0<=p -> (n|p) -> (m|p) ->
 (forall q, (n|q) -> (m|q) -> (p|q)) ->
 lcm n m == p.
Proof.
 intros n m p Hp Hn Hm H.
 apply divide_antisym; trivial.
 now apply lcm_least.
 apply H. apply divide_lcm_l. apply divide_lcm_r.
Qed.

Lemma lcm_unique_alt : forall n m p, 0<=p ->
 (forall q, (p|q) <-> (n|q) /\ (m|q)) ->
 lcm n m == p.
Proof.
 intros n m p Hp H.
 apply lcm_unique; trivial.
 apply H, divide_refl.
 apply H, divide_refl.
 intros. apply H. now split.
Qed.

Lemma lcm_assoc : forall n m p, lcm n (lcm m p) == lcm (lcm n m) p.
Proof.
 intros. apply lcm_unique_alt. apply le_0_l.
 intros. now rewrite !lcm_divide_iff, and_assoc.
Qed.

Lemma lcm_0_l : forall n, lcm 0 n == 0.
Proof.
 intros. apply lcm_unique; trivial. order.
 apply divide_refl.
 apply divide_0_r.
Qed.

Lemma lcm_0_r : forall n, lcm n 0 == 0.
Proof.
 intros. now rewrite lcm_comm, lcm_0_l.
Qed.

Lemma lcm_1_l : forall n, lcm 1 n == n.
Proof.
 intros. apply lcm_unique; trivial using divide_1_l, le_0_l, divide_refl.
Qed.

Lemma lcm_1_r : forall n, lcm n 1 == n.
Proof.
 intros. now rewrite lcm_comm, lcm_1_l.
Qed.

Lemma lcm_diag : forall n, lcm n n == n.
Proof.
 intros. apply lcm_unique; trivial using divide_refl, le_0_l.
Qed.

Lemma lcm_eq_0 : forall n m, lcm n m == 0 <-> n == 0 \/ m == 0.
Proof.
 intros. split.
 intros EQ.
 apply eq_mul_0.
 apply divide_0_l. rewrite <- EQ. apply lcm_least.
  apply divide_factor_l. apply divide_factor_r.
 destruct 1 as [EQ|EQ]; rewrite EQ. apply lcm_0_l. apply lcm_0_r.
Qed.

Lemma divide_lcm_eq_r : forall n m, (n|m) -> lcm n m == m.
Proof.
 intros n m H. apply lcm_unique_alt; trivial using le_0_l.
 intros q. split. split; trivial. now transitivity m.
 now destruct 1.
Qed.

Lemma divide_lcm_iff : forall n m, (n|m) <-> lcm n m == m.
Proof.
 intros n m. split. now apply divide_lcm_eq_r.
 intros EQ. rewrite <- EQ. apply divide_lcm_l.
Qed.

Lemma lcm_mul_mono_l :
  forall n m p, lcm (p * n) (p * m) == p * lcm n m.
Proof.
 intros n m p.
 destruct (eq_decidable p 0) as [Hp|Hp].
  rewrite Hp. nzsimpl. rewrite lcm_0_l. now nzsimpl.
 destruct (eq_decidable (gcd n m) 0) as [Hg|Hg].
  apply gcd_eq_0 in Hg. destruct Hg as (Hn,Hm); rewrite Hn, Hm.
  nzsimpl. rewrite lcm_0_l. now nzsimpl.
 unfold lcm.
 rewrite gcd_mul_mono_l.
 rewrite mul_assoc. f_equiv.
 now rewrite div_mul_cancel_l.
Qed.

Lemma lcm_mul_mono_r :
 forall n m p, lcm (n * p) (m * p) == lcm n m * p.
Proof.
 intros n m p. now rewrite !(mul_comm _ p), lcm_mul_mono_l, mul_comm.
Qed.

Lemma gcd_1_lcm_mul : forall n m, n~=0 -> m~=0 ->
 (gcd n m == 1 <-> lcm n m == n*m).
Proof.
 intros n m Hn Hm. split; intros H.
 unfold lcm. rewrite H. now rewrite div_1_r.
 unfold lcm in *.
 apply mul_cancel_l in H; trivial.
 assert (Hg : gcd n m ~= 0) by (red; rewrite gcd_eq_0; destruct 1; order).
 assert (H' := gcd_divide_r n m).
 apply mod_divide in H'; trivial. apply div_exact in H'; trivial.
 rewrite H in H'.
 rewrite <- (mul_1_l m) in H' at 1.
 now apply mul_cancel_r in H'.
Qed.

End NLcmProp.
