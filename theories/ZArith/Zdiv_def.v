(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos BinNat BinInt Zbool Zcompare Zorder Zabs Nnat Ndiv_def.
Local Open Scope Z_scope.

(** * Definitions of divisions for binary integers *)

(** Concerning the many possible variants of integer divisions, see:

    R. Boute, "The Euclidean definition of the functions div and mod",
    ACM Transactions on Programming Languages and Systems,
    Vol. 14, No.2, pp. 127-144, April 1992.

   We provide here two flavours:

    - convention Floor (F) : [Zdiv_eucl], [Zdiv], [Zmod]
    - convention Trunc (T) : [Zquotrem], [Zquot], [Zrem]

   A third one, the Euclid (E) convention, can be found in file
   Zeuclid.v

   For non-zero b, they all satisfy [a = b*(a/b) + (a mod b)]
   and [ |a mod b| < |b| ], but the sign of the modulo will differ
   when [a<0] and/or [b<0].

*)

(** * Floor *)

(** [Zdiv_eucl] provides a Truncated-Toward-Bottom (a.k.a Floor)
  Euclidean division. Its projections are named [Zdiv] and [Zmod].
  These functions correspond to the `div` and `mod` of Haskell.
  This is the historical convention of Coq.

  The main properties of this convention are :
    - we have [sgn (a mod b) = sgn (b)]
    - [div a b] is the greatest integer smaller or equal to the exact
      fraction [a/b].
    - there is no easy sign rule.

  In addition, note that we arbitrary take [a/0 = 0] and [a mod 0 = 0].
*)

(** First, a division for positive numbers. Even if the second
   argument is a Z, the answer is arbitrary is it isn't a Zpos. *)

Fixpoint Zdiv_eucl_POS (a:positive) (b:Z) : Z * Z :=
  match a with
    | xH => if Zge_bool b 2 then (0, 1) else (1, 0)
    | xO a' =>
      let (q, r) := Zdiv_eucl_POS a' b in
	let r' := 2 * r in
	  if Zgt_bool b r' then (2 * q, r') else (2 * q + 1, r' - b)
    | xI a' =>
      let (q, r) := Zdiv_eucl_POS a' b in
	let r' := 2 * r + 1 in
	  if Zgt_bool b r' then (2 * q, r') else (2 * q + 1, r' - b)
  end.

(** Then the general euclidean division *)

Definition Zdiv_eucl (a b:Z) : Z * Z :=
  match a, b with
    | 0, _ => (0, 0)
    | _, 0 => (0, 0)
    | Zpos a', Zpos _ => Zdiv_eucl_POS a' b
    | Zneg a', Zpos _ =>
      let (q, r) := Zdiv_eucl_POS a' b in
	match r with
	  | 0 => (- q, 0)
	  | _ => (- (q + 1), b - r)
	end
    | Zneg a', Zneg b' =>
      let (q, r) := Zdiv_eucl_POS a' (Zpos b') in (q, - r)
    | Zpos a', Zneg b' =>
      let (q, r) := Zdiv_eucl_POS a' (Zpos b') in
	match r with
	  | 0 => (- q, 0)
	  | _ => (- (q + 1), b + r)
	end
  end.

Definition Zdiv (a b:Z) : Z := let (q, _) := Zdiv_eucl a b in q.
Definition Zmod (a b:Z) : Z := let (_, r) := Zdiv_eucl a b in r.

Infix "/" := Zdiv : Z_scope.
Infix "mod" := Zmod (at level 40, no associativity) : Z_scope.


(** * Trunc *)

(** [Zquotrem] provides a Truncated-Toward-Zero Euclidean division.
  Its projections are named [Zquot] and [Zrem]. These functions
  correspond to the `quot` and `rem` of Haskell, and this division
  convention is used in most programming languages, e.g. Ocaml.

  With this convention:
   - we have [sgn(a rem b) = sgn(a)]
   - sign rule for division: [quot (-a) b = quot a (-b) = -(quot a b)]
   - and for modulo: [a rem (-b) = a rem b] and [(-a) rem b = -(a rem b)]

 Note that we arbitrary take here [quot a 0 = 0] and [a rem 0 = a].
*)

Definition Zquotrem (a b:Z) : Z * Z :=
  match a, b with
   | 0,  _ => (0, 0)
   | _, 0  => (0, a)
   | Zpos a, Zpos b =>
     let (q, r) := Pdiv_eucl a b in (Z_of_N q, Z_of_N r)
   | Zneg a, Zpos b =>
     let (q, r) := Pdiv_eucl a b in (- Z_of_N q, - Z_of_N r)
   | Zpos a, Zneg b =>
     let (q, r) := Pdiv_eucl a b in (- Z_of_N q, Z_of_N r)
   | Zneg a, Zneg b =>
     let (q, r) := Pdiv_eucl a b in (Z_of_N q, - Z_of_N r)
  end.

Definition Zquot a b := fst (Zquotrem a b).
Definition Zrem a b := snd (Zquotrem a b).

Infix "÷" := Zquot (at level 40, left associativity) : Z_scope.
(** No infix notation for rem, otherwise it becomes a keyword *)

(** * Correctness proofs *)

(** Correctness proofs for Trunc *)

Lemma Zdiv_eucl_POS_eq : forall a b, 0 < b ->
  let (q, r) := Zdiv_eucl_POS a b in Zpos a = b * q + r.
Proof.
 intros a b Hb.
 induction a; cbv beta iota delta [Zdiv_eucl_POS]; fold Zdiv_eucl_POS.
 (* ~1 *)
 destruct Zdiv_eucl_POS as (q,r); cbv zeta.
 rewrite Zpos_xI, IHa, Zmult_plus_distr_r, Zmult_permute.
 destruct Zgt_bool.
 now rewrite Zplus_assoc.
 now rewrite Zmult_plus_distr_r, Zmult_1_r, <- !Zplus_assoc, Zplus_minus.
 (* ~0 *)
 destruct Zdiv_eucl_POS as (q,r); cbv zeta.
 rewrite (Zpos_xO a), IHa, Zmult_plus_distr_r, Zmult_permute.
 destruct Zgt_bool; trivial.
 now rewrite Zmult_plus_distr_r, Zmult_1_r, <- !Zplus_assoc, Zplus_minus.
 (* ~1 *)
 generalize (Zge_cases b 2); destruct Zge_bool; intros Hb'.
 now rewrite Zmult_0_r.
 replace b with 1. reflexivity.
 apply Zle_antisym. now apply Zlt_le_succ in Hb. now apply Zlt_succ_le.
Qed.

Lemma Zdiv_eucl_eq : forall a b, b<>0 ->
 let (q, r) := Zdiv_eucl a b in a = b * q + r.
Proof.
 intros [ |a|a] [ |b|b]; unfold Zdiv_eucl; trivial;
  (now destruct 1) || intros _;
  generalize (Zdiv_eucl_POS_eq a (Zpos b) (eq_refl _));
  destruct Zdiv_eucl_POS as (q,r); try change (Zneg a) with (-Zpos a);
  intros ->.
 (* Zpos Zpos *)
 reflexivity.
 (* Zpos Zneg *)
 rewrite <- (Zopp_neg b), Zmult_opp_comm.
 destruct r as [ |r|r]; trivial.
 rewrite Zopp_plus_distr, Zmult_plus_distr_r, <- Zplus_assoc. f_equal.
 now rewrite <- Zmult_opp_comm, Zmult_1_r, Zplus_assoc, Zplus_opp_l.
 rewrite Zopp_plus_distr, Zmult_plus_distr_r, <- Zplus_assoc. f_equal.
 now rewrite <- Zmult_opp_comm, Zmult_1_r, Zplus_assoc, Zplus_opp_l.
 (* Zneg Zpos *)
 rewrite (Zopp_plus_distr _ r), Zopp_mult_distr_r.
 destruct r as [ |r|r]; trivial; unfold Zminus.
 rewrite Zopp_plus_distr, Zmult_plus_distr_r, <- Zplus_assoc. f_equal.
 now rewrite <- Zmult_opp_comm, Zmult_1_r, Zplus_assoc, Zplus_opp_l.
 rewrite Zopp_plus_distr, Zmult_plus_distr_r, <- Zplus_assoc. f_equal.
 now rewrite <- Zmult_opp_comm, Zmult_1_r, Zplus_assoc, Zplus_opp_l.
 (* Zneg Zneg *)
 now rewrite (Zopp_plus_distr _ r), Zopp_mult_distr_l.
Qed.

Lemma Z_div_mod_eq_full : forall a b, b<>0 -> a = b*(a/b) + (a mod b).
Proof.
 intros a b Hb. generalize (Zdiv_eucl_eq a b Hb).
 unfold Zdiv, Zmod. now destruct Zdiv_eucl.
Qed.

Lemma Zmod_POS_bound : forall a b, 0<b -> 0 <= snd (Zdiv_eucl_POS a b) < b.
Proof.
 assert (AUX : forall a p, a < Zpos (p~0) -> a - Zpos p < Zpos p).
  intros. unfold Zminus. apply Zlt_plus_swap. unfold Zminus.
  now rewrite Zopp_involutive, Zplus_diag_eq_mult_2, Zmult_comm.
 intros a [|b|b] Hb; discriminate Hb || clear Hb.
 induction a; cbv beta iota delta [Zdiv_eucl_POS]; fold Zdiv_eucl_POS.
 (* ~1 *)
 destruct Zdiv_eucl_POS as (q,r). cbv zeta.
 simpl in IHa; destruct IHa as (Hr,Hr').
 generalize (Zgt_cases (Zpos b) (2*r+1)). destruct Zgt_bool.
 unfold snd in *.
 split. apply Zplus_le_0_compat. now apply Zmult_le_0_compat. easy.
  now apply Zgt_lt.
 unfold snd in *.
 split. now apply Zle_minus_le_0.
  apply AUX.
  destruct r as [|r|r]; try (now destruct Hr); try easy.
  red. simpl. apply Pcompare_eq_Lt. exact Hr'.
 (* ~0 *)
 destruct Zdiv_eucl_POS as (q,r). cbv zeta.
 simpl in IHa; destruct IHa as (Hr,Hr').
 generalize (Zgt_cases (Zpos b) (2*r)). destruct Zgt_bool.
 unfold snd in *.
 split. now apply Zmult_le_0_compat.
  now apply Zgt_lt.
 unfold snd in *.
 split. now apply Zle_minus_le_0.
  apply AUX.
  destruct r as [|r|r]; try (now destruct Hr); try easy.
 (* 1 *)
 generalize (Zge_cases (Zpos b) 2). destruct Zge_bool; simpl.
 split. easy. now apply Zle_succ_l, Zge_le.
 now split.
Qed.

Lemma Zmod_pos_bound : forall a b, 0 < b -> 0 <= a mod b < b.
Proof.
 intros a [|b|b] Hb; discriminate Hb || clear Hb.
 destruct a as [|a|a]; unfold Zmod, Zdiv_eucl.
 now split.
 now apply Zmod_POS_bound.
 generalize (Zmod_POS_bound a (Zpos b) (eq_refl _)).
 destruct Zdiv_eucl_POS as (q,r). unfold snd. intros (Hr,Hr').
 destruct r as [|r|r]; (now destruct Hr) || clear Hr.
 now split.
 split. now apply Zlt_le_weak, Zlt_plus_swap.
 now apply Zlt_minus_simpl_swap.
Qed.

Lemma Zmod_neg_bound : forall a b, b < 0 -> b < a mod b <= 0.
Proof.
 intros a [|b|b] Hb; discriminate Hb || clear Hb.
 destruct a as [|a|a]; unfold Zmod, Zdiv_eucl.
 now split.
 generalize (Zmod_POS_bound a (Zpos b) (eq_refl _)).
 destruct Zdiv_eucl_POS as (q,r). unfold snd. intros (Hr,Hr').
 destruct r as [|r|r]; (now destruct Hr) || clear Hr.
 now split.
 split. rewrite Zplus_comm. now apply (Zplus_lt_compat_r 0).
 rewrite Zplus_comm. apply Zle_plus_swap. simpl. now apply Zlt_le_weak.
 generalize (Zmod_POS_bound a (Zpos b) (eq_refl _)).
 destruct Zdiv_eucl_POS as (q,r). unfold snd. intros (Hr,Hr').
 split. red in Hr'. now rewrite Zcompare_opp in Hr'. now destruct r.
Qed.

(** Correctness proofs for Floor *)

Theorem Zquotrem_eq: forall a b,
  let (q,r) := Zquotrem a b in a = q * b + r.
Proof.
 destruct a, b; simpl; trivial;
 generalize (Pdiv_eucl_correct p p0); case Pdiv_eucl; trivial;
  intros q r H; try change (Zneg p) with (-Zpos p);
  rewrite <- (Z_of_N_pos p), H, Z_of_N_plus, Z_of_N_mult; f_equal.
 now rewrite Zmult_opp_comm.
 now rewrite Zopp_plus_distr, Zopp_mult_distr_l.
 now rewrite Zopp_plus_distr, Zopp_mult_distr_r.
Qed.

Lemma Z_quot_rem_eq : forall a b, a = b*(a÷b) + Zrem a b.
Proof.
 intros a b. rewrite Zmult_comm. generalize (Zquotrem_eq a b).
 unfold Zquot, Zrem. now destruct Zquotrem.
Qed.

Lemma Zrem_bound : forall a b, 0<=a -> 0<b -> 0 <= Zrem a b < b.
Proof.
 intros a [|b|b] Ha Hb; discriminate Hb || clear Hb.
 destruct a as [|a|a]; (now destruct Ha) || clear Ha.
 compute. now split.
 unfold Zrem, Zquotrem.
 generalize (Pdiv_eucl_remainder a b). destruct Pdiv_eucl as (q,r).
 simpl. split. apply Z_of_N_le_0.
 destruct r; red; simpl; trivial.
Qed.

Lemma Zrem_opp_l : forall a b, Zrem (-a) b = - (Zrem a b).
Proof.
 intros [|a|a] [|b|b]; trivial; unfold Zrem;
  simpl; destruct Pdiv_eucl; simpl; try rewrite Zopp_involutive; trivial.
Qed.

Lemma Zrem_opp_r : forall a b, Zrem a (-b) = Zrem a b.
Proof.
 intros [|a|a] [|b|b]; trivial; unfold Zrem; simpl;
  destruct Pdiv_eucl; simpl; try rewrite Zopp_involutive; trivial.
Qed.
