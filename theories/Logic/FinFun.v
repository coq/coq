(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Functions on finite domains *)

(** Main result : for functions [f:A->A] with finite [A],
    f injective <-> f bijective <-> f surjective. *)

Require Import List Compare_dec EqNat Decidable ListDec. Require Fin.
Set Implicit Arguments.

(** General definitions *)

Definition Injective {A B} (f : A->B) :=
 forall x y, f x = f y -> x = y.

Definition Surjective {A B} (f : A->B) :=
 forall y, exists x, f x = y.

Definition Bijective {A B} (f : A->B) :=
 exists g:B->A, (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

(** Finiteness is defined here via exhaustive list enumeration *)

Definition Full {A:Type} (l:list A) := forall a:A, In a l.
Definition Finite (A:Type) := exists (l:list A), Full l.

(** In many following proofs, it will be convenient to have
    list enumerations without duplicates. As soon as we have
    decidability of equality (in Prop), this is equivalent
    to the previous notion. *)

Definition Listing {A:Type} (l:list A) := NoDup l /\ Full l.
Definition Finite' (A:Type) := exists (l:list A), Listing l.

Lemma Finite_alt A (d:decidable_eq A) : Finite A <-> Finite' A.
Proof.
 split.
 - intros (l,F). destruct (uniquify d l) as (l' & N & I).
   exists l'. split; trivial.
   intros x. apply I, F.
 - intros (l & _ & F). now exists l.
Qed.

(** Injections characterized in term of lists *)

Lemma Injective_map_NoDup A B (f:A->B) (l:list A) :
 Injective f -> NoDup l -> NoDup (map f l).
Proof.
 intros Ij. induction 1 as [|x l X N IH]; simpl; constructor; trivial.
 rewrite in_map_iff. intros (y & E & Y). apply Ij in E. now subst.
Qed.

Lemma Injective_list_carac A B (d:decidable_eq A)(f:A->B) :
  Injective f <-> (forall l, NoDup l -> NoDup (map f l)).
Proof.
 split.
 - intros. now apply Injective_map_NoDup.
 - intros H x y E.
   destruct (d x y); trivial.
   assert (N : NoDup (x::y::nil)).
   { repeat constructor; simpl; intuition. }
   specialize (H _ N). simpl in H. rewrite E in H.
   inversion_clear H; simpl in *; intuition.
Qed.

Lemma Injective_carac A B (l:list A) : Listing l ->
   forall (f:A->B), Injective f <-> NoDup (map f l).
Proof.
 intros L f. split.
 - intros Ij. apply Injective_map_NoDup; trivial. apply L.
 - intros N x y E.
   assert (X : In x l) by apply L.
   assert (Y : In y l) by apply L.
   apply In_nth_error in X. destruct X as (i,X).
   apply In_nth_error in Y. destruct Y as (j,Y).
   assert (X' := map_nth_error f _ _ X).
   assert (Y' := map_nth_error f _ _ Y).
   assert (i = j).
   { rewrite NoDup_nth_error in N. apply N.
     - rewrite <- nth_error_Some. now rewrite X'.
     - rewrite X', Y'. now f_equal. }
   subst j. rewrite Y in X. now injection X.
Qed.

(** Surjection characterized in term of lists *)

Lemma Surjective_list_carac A B (f:A->B):
  Surjective f <-> (forall lB, exists lA, incl lB (map f lA)).
Proof.
 split.
 - intros Su.
   induction lB as [|b lB IH].
   + now exists nil.
   + destruct (Su b) as (a,E).
     destruct IH as (lA,IC).
     exists (a::lA). simpl. rewrite E.
     intros x [X|X]; simpl; intuition.
 - intros H y.
   destruct (H (y::nil)) as (lA,IC).
   assert (IN : In y (map f lA)) by (apply (IC y); now left).
   rewrite in_map_iff in IN. destruct IN as (x & E & _).
   now exists x.
Qed.

Lemma Surjective_carac A B : Finite B -> decidable_eq B ->
  forall f:A->B, Surjective f <-> (exists lA, Listing (map f lA)).
Proof.
 intros (lB,FB) d. split.
 - rewrite Surjective_list_carac.
   intros Su. destruct (Su lB) as (lA,IC).
   destruct (uniquify_map d f lA) as (lA' & N & IC').
   exists lA'. split; trivial.
   intro x. apply IC', IC, FB.
 - intros (lA & N & FA) y.
   generalize (FA y). rewrite in_map_iff. intros (x & E & _).
   now exists x.
Qed.

(** Main result : *)

Lemma Endo_Injective_Surjective :
 forall A, Finite A -> decidable_eq A ->
  forall f:A->A, Injective f <-> Surjective f.
Proof.
 intros A F d f. rewrite (Surjective_carac F d). split.
 - apply (Finite_alt d) in F. destruct F as (l,L).
   rewrite (Injective_carac L); intros.
   exists l; split; trivial.
   destruct L as (N,F).
   assert (I : incl l (map f l)).
   { apply NoDup_length_incl; trivial.
     - now rewrite map_length.
     - intros x _. apply F. }
   intros x. apply I, F.
 - clear F d. intros (l,L).
   assert (N : NoDup l). { apply (NoDup_map_inv f), L. }
   assert (I : incl (map f l) l).
   { apply NoDup_length_incl; trivial.
     - now rewrite map_length.
     - intros x _. apply L. }
   assert (L' : Listing l).
   { split; trivial.
     intro x. apply I, L. }
   apply (Injective_carac L'), L.
Qed.

(** An injective and surjective function is bijective.
    We need here stronger hypothesis : decidability of equality in Type. *)

Definition EqDec (A:Type) := forall x y:A, {x=y}+{x<>y}.

(** First, we show that a surjective f has an inverse function g such that
    f.g = id. *)

(* NB: instead of (Finite A), we could ask for (RecEnum A) with:
Definition RecEnum A := exists h:nat->A, surjective h.
*)

Lemma Finite_Empty_or_not A :
  Finite A -> (A->False) \/ exists a:A,True.
Proof.
 intros (l,F).
 destruct l.
 - left; exact F.
 - right; now exists a.
Qed.

Lemma Surjective_inverse :
  forall A B, Finite A -> EqDec B ->
   forall f:A->B, Surjective f ->
    exists g:B->A, forall x, f (g x) = x.
Proof.
 intros A B F d f Su.
 destruct (Finite_Empty_or_not F) as [noA | (a,_)].
 - (* A is empty : g is obtained via False_rect *)
   assert (noB : B -> False). { intros y. now destruct (Su y). }
   exists (fun y => False_rect _ (noB y)).
   intro y. destruct (noB y).
 - (* A is inhabited by a : we use it in Option.get *)
   destruct F as (l,F).
   set (h := fun x k => if d (f k) x then true else false).
   set (get := fun o => match o with Some y => y | None => a end).
   exists (fun x => get (List.find (h x) l)).
   intros x.
   case_eq (find (h x) l); simpl; clear get; [intros y H|intros H].
   * apply find_some in H. destruct H as (_,H). unfold h in H.
     now destruct (d (f y) x) in H.
   * exfalso.
     destruct (Su x) as (y & Y).
     generalize (find_none _ l H y (F y)).
     unfold h. now destruct (d (f y) x).
Qed.

(** Same, with more knowledge on the inverse function: g.f = f.g = id *)

Lemma Injective_Surjective_Bijective :
 forall A B, Finite A -> EqDec B ->
  forall f:A->B, Injective f -> Surjective f -> Bijective f.
Proof.
 intros A B F d f Ij Su.
 destruct (Surjective_inverse F d Su) as (g, E).
 exists g. split; trivial.
 intros y. apply Ij. now rewrite E.
Qed.


(** An example of finite type : [Fin.t] *)

Lemma Fin_Finite n : Finite (Fin.t n).
Proof.
 induction n.
 - exists nil.
   red;inversion a.
 - destruct IHn as (l,Hl).
   exists (Fin.F1 :: map Fin.FS l).
   intros a. revert n a l Hl.
   refine (@Fin.caseS _ _ _); intros.
   + now left.
   + right. now apply in_map.
Qed.

(** Instead of working on a finite subset of nat, another
    solution is to use restricted [nat->nat] functions, and
    to consider them only below a certain bound [n]. *)

Definition bFun n (f:nat->nat) := forall x, x < n -> f x < n.

Definition bInjective n (f:nat->nat) :=
 forall x y, x < n -> y < n -> f x = f y -> x = y.

Definition bSurjective n (f:nat->nat) :=
 forall y, y < n -> exists x, x < n /\ f x = y.

(** We show that this is equivalent to the use of [Fin.t n]. *)

Module Fin2Restrict.

Notation n2f := Fin.of_nat_lt.
Definition f2n {n} (x:Fin.t n) := proj1_sig (Fin.to_nat x).
Definition f2n_ok n (x:Fin.t n) : f2n x < n := proj2_sig (Fin.to_nat x).
Definition n2f_f2n : forall n x, n2f (f2n_ok x) = x := @Fin.of_nat_to_nat_inv.
Definition f2n_n2f x n h : f2n (n2f h) = x := f_equal (@proj1_sig _ _) (@Fin.to_nat_of_nat x n h).
Definition n2f_ext : forall x n h h', n2f h = n2f h' := @Fin.of_nat_ext.
Definition f2n_inj : forall n x y, f2n x = f2n y -> x = y := @Fin.to_nat_inj.

Definition extend n (f:Fin.t n -> Fin.t n) : (nat->nat) :=
 fun x =>
   match le_lt_dec n x with
     | left _ => 0
     | right h => f2n (f (n2f h))
   end.

Definition restrict n (f:nat->nat)(hf : bFun n f) : (Fin.t n -> Fin.t n) :=
 fun x => let (x',h) := Fin.to_nat x in n2f (hf _ h).

Ltac break_dec H :=
 let H' := fresh "H" in
 destruct le_lt_dec as [H'|H'];
  [elim (Lt.le_not_lt _ _ H' H)
  |try rewrite (n2f_ext H' H) in *; try clear H'].

Lemma extend_ok n f : bFun n (@extend n f).
Proof.
 intros x h. unfold extend. break_dec h. apply f2n_ok.
Qed.

Lemma extend_f2n n f (x:Fin.t n) : extend f (f2n x) = f2n (f x).
Proof.
 generalize (n2f_f2n x). unfold extend, f2n, f2n_ok.
 destruct (Fin.to_nat x) as (x',h); simpl.
 break_dec h.
 now intros ->.
Qed.

Lemma extend_n2f n f x (h:x<n) : n2f (extend_ok f h) = f (n2f h).
Proof.
 generalize (extend_ok f h). unfold extend in *. break_dec h. intros h'.
 rewrite <- n2f_f2n. now apply n2f_ext.
Qed.

Lemma restrict_f2n n f hf (x:Fin.t n) :
 f2n (@restrict n f hf x) = f (f2n x).
Proof.
 unfold restrict, f2n. destruct (Fin.to_nat x) as (x',h); simpl.
 apply f2n_n2f.
Qed.

Lemma restrict_n2f n f hf x (h:x<n) :
 @restrict n f hf (n2f h) = n2f (hf _ h).
Proof.
 unfold restrict. generalize (f2n_n2f h). unfold f2n.
 destruct (Fin.to_nat (n2f h)) as (x',h'); simpl. intros ->.
 now apply n2f_ext.
Qed.

Lemma extend_surjective n f :
  bSurjective n (@extend n f) <-> Surjective f.
Proof.
 split.
 - intros hf y.
   destruct (hf _ (f2n_ok y)) as (x & h & Eq).
   exists (n2f h).
   apply f2n_inj. now rewrite <- Eq, <- extend_f2n, f2n_n2f.
 - intros hf y hy.
   destruct (hf (n2f hy)) as (x,Eq).
   exists (f2n x).
   split.
   + apply f2n_ok.
   + rewrite extend_f2n, Eq. apply f2n_n2f.
Qed.

Lemma extend_injective n f :
  bInjective n (@extend n f) <-> Injective f.
Proof.
 split.
 - intros hf x y Eq.
   apply f2n_inj. apply hf; try apply f2n_ok.
   now rewrite 2 extend_f2n, Eq.
 - intros hf x y hx hy Eq.
   rewrite <- (f2n_n2f hx), <- (f2n_n2f hy). f_equal.
   apply hf.
   rewrite <- 2 extend_n2f.
   generalize (extend_ok f hx) (extend_ok f hy).
   rewrite Eq. apply n2f_ext.
Qed.

Lemma restrict_surjective n f h :
  Surjective (@restrict n f h) <-> bSurjective n f.
Proof.
 split.
 - intros hf y hy.
   destruct (hf (n2f hy)) as (x,Eq).
   exists (f2n x).
   split.
   + apply f2n_ok.
   + rewrite <- (restrict_f2n h), Eq. apply f2n_n2f.
 - intros hf y.
   destruct (hf _ (f2n_ok y)) as (x & hx & Eq).
   exists (n2f hx).
   apply f2n_inj. now rewrite restrict_f2n, f2n_n2f.
Qed.

Lemma restrict_injective n f h :
  Injective (@restrict n f h) <-> bInjective n f.
Proof.
 split.
 - intros hf x y hx hy Eq.
   rewrite <- (f2n_n2f hx), <- (f2n_n2f hy). f_equal.
   apply hf.
   rewrite 2 restrict_n2f.
   generalize (h x hx) (h y hy).
   rewrite Eq. apply n2f_ext.
 - intros hf x y Eq.
   apply f2n_inj. apply hf; try apply f2n_ok.
   now rewrite <- 2 (restrict_f2n h), Eq.
Qed.

End Fin2Restrict.
Import Fin2Restrict.

(** We can now use Proof via the equivalence ... *)

Lemma bInjective_bSurjective n (f:nat->nat) :
 bFun n f -> (bInjective n f <-> bSurjective n f).
Proof.
 intros h.
 rewrite <- (restrict_injective h), <- (restrict_surjective h).
 apply Endo_Injective_Surjective.
 - apply Fin_Finite.
 - intros x y. destruct (Fin.eq_dec x y); [left|right]; trivial.
Qed.

Lemma bSurjective_bBijective n (f:nat->nat) :
 bFun n f -> bSurjective n f ->
 exists g, bFun n g /\ forall x, x < n -> g (f x) = x /\ f (g x) = x.
Proof.
 intro hf.
 rewrite <- (restrict_surjective hf). intros Su.
 assert (Ij : Injective (restrict hf)).
 { apply Endo_Injective_Surjective; trivial.
   - apply Fin_Finite.
   - intros x y. destruct (Fin.eq_dec x y); [left|right]; trivial. }
 assert (Bi : Bijective (restrict hf)).
 { apply Injective_Surjective_Bijective; trivial.
   - apply Fin_Finite.
   - exact Fin.eq_dec. }
 destruct Bi as (g & Hg & Hg').
 exists (extend g).
 split.
 - apply extend_ok.
 - intros x Hx. split.
   + now rewrite <- (f2n_n2f Hx), <- (restrict_f2n hf), extend_f2n, Hg.
   + now rewrite <- (f2n_n2f Hx), extend_f2n, <- (restrict_f2n hf), Hg'.
Qed.
