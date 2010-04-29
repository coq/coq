(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import LegacyRing_theory.
Require Import Quote.
Require Import Ring_normalize.

Unset Boxed Definitions.

Section abstract_semi_rings.

Inductive aspolynomial : Type :=
  | ASPvar : index -> aspolynomial
  | ASP0 : aspolynomial
  | ASP1 : aspolynomial
  | ASPplus : aspolynomial -> aspolynomial -> aspolynomial
  | ASPmult : aspolynomial -> aspolynomial -> aspolynomial.

Inductive abstract_sum : Type :=
  | Nil_acs : abstract_sum
  | Cons_acs : varlist -> abstract_sum -> abstract_sum.

Fixpoint abstract_sum_merge (s1:abstract_sum) :
 abstract_sum -> abstract_sum :=
  match s1 with
  | Cons_acs l1 t1 =>
      (fix asm_aux (s2:abstract_sum) : abstract_sum :=
         match s2 with
         | Cons_acs l2 t2 =>
             if varlist_lt l1 l2
             then Cons_acs l1 (abstract_sum_merge t1 s2)
             else Cons_acs l2 (asm_aux t2)
         | Nil_acs => s1
         end)
  | Nil_acs => fun s2 => s2
  end.

Fixpoint abstract_varlist_insert (l1:varlist) (s2:abstract_sum) {struct s2} :
 abstract_sum :=
  match s2 with
  | Cons_acs l2 t2 =>
      if varlist_lt l1 l2
      then Cons_acs l1 s2
      else Cons_acs l2 (abstract_varlist_insert l1 t2)
  | Nil_acs => Cons_acs l1 Nil_acs
  end.

Fixpoint abstract_sum_scalar (l1:varlist) (s2:abstract_sum) {struct s2} :
 abstract_sum :=
  match s2 with
  | Cons_acs l2 t2 =>
      abstract_varlist_insert (varlist_merge l1 l2)
        (abstract_sum_scalar l1 t2)
  | Nil_acs => Nil_acs
  end.

Fixpoint abstract_sum_prod (s1 s2:abstract_sum) {struct s1} : abstract_sum :=
  match s1 with
  | Cons_acs l1 t1 =>
      abstract_sum_merge (abstract_sum_scalar l1 s2)
        (abstract_sum_prod t1 s2)
  | Nil_acs => Nil_acs
  end.

Fixpoint aspolynomial_normalize (p:aspolynomial) : abstract_sum :=
  match p with
  | ASPvar i => Cons_acs (Cons_var i Nil_var) Nil_acs
  | ASP1 => Cons_acs Nil_var Nil_acs
  | ASP0 => Nil_acs
  | ASPplus l r =>
      abstract_sum_merge (aspolynomial_normalize l)
        (aspolynomial_normalize r)
  | ASPmult l r =>
      abstract_sum_prod (aspolynomial_normalize l) (aspolynomial_normalize r)
  end.



Variable A : Type.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aeq : A -> A -> bool.
Variable vm : varmap A.
Variable T : Semi_Ring_Theory Aplus Amult Aone Azero Aeq.

Fixpoint interp_asp (p:aspolynomial) : A :=
  match p with
  | ASPvar i => interp_var Azero vm i
  | ASP0 => Azero
  | ASP1 => Aone
  | ASPplus l r => Aplus (interp_asp l) (interp_asp r)
  | ASPmult l r => Amult (interp_asp l) (interp_asp r)
  end.

(* Local *) Definition iacs_aux :=
              (fix iacs_aux (a:A) (s:abstract_sum) {struct s} : A :=
                 match s with
                 | Nil_acs => a
                 | Cons_acs l t =>
                     Aplus a (iacs_aux (interp_vl Amult Aone Azero vm l) t)
                 end).

Definition interp_acs (s:abstract_sum) : A :=
  match s with
  | Cons_acs l t => iacs_aux (interp_vl Amult Aone Azero vm l) t
  | Nil_acs => Azero
  end.

Hint Resolve (SR_plus_comm T).
Hint Resolve (SR_plus_assoc T).
Hint Resolve (SR_plus_assoc2 T).
Hint Resolve (SR_mult_comm T).
Hint Resolve (SR_mult_assoc T).
Hint Resolve (SR_mult_assoc2 T).
Hint Resolve (SR_plus_zero_left T).
Hint Resolve (SR_plus_zero_left2 T).
Hint Resolve (SR_mult_one_left T).
Hint Resolve (SR_mult_one_left2 T).
Hint Resolve (SR_mult_zero_left T).
Hint Resolve (SR_mult_zero_left2 T).
Hint Resolve (SR_distr_left T).
Hint Resolve (SR_distr_left2 T).
(*Hint Resolve (SR_plus_reg_left T).*)
Hint Resolve (SR_plus_permute T).
Hint Resolve (SR_mult_permute T).
Hint Resolve (SR_distr_right T).
Hint Resolve (SR_distr_right2 T).
Hint Resolve (SR_mult_zero_right T).
Hint Resolve (SR_mult_zero_right2 T).
Hint Resolve (SR_plus_zero_right T).
Hint Resolve (SR_plus_zero_right2 T).
Hint Resolve (SR_mult_one_right T).
Hint Resolve (SR_mult_one_right2 T).
(*Hint Resolve (SR_plus_reg_right T).*)
Hint Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
Hint Immediate T.

Remark iacs_aux_ok :
 forall (x:A) (s:abstract_sum), iacs_aux x s = Aplus x (interp_acs s).
Proof.
  simple induction s; simpl in |- *; intros.
  trivial.
  reflexivity.
Qed.

Hint Extern 10 (_ = _ :>A) => rewrite iacs_aux_ok: core.

Lemma abstract_varlist_insert_ok :
 forall (l:varlist) (s:abstract_sum),
   interp_acs (abstract_varlist_insert l s) =
   Aplus (interp_vl Amult Aone Azero vm l) (interp_acs s).

  simple induction s.
  trivial.

  simpl in |- *; intros.
  elim (varlist_lt l v); simpl in |- *.
  eauto.
  rewrite iacs_aux_ok.
  rewrite H; auto.

Qed.

Lemma abstract_sum_merge_ok :
 forall x y:abstract_sum,
   interp_acs (abstract_sum_merge x y) = Aplus (interp_acs x) (interp_acs y).

Proof.
  simple induction x.
  trivial.
  simple induction y; intros.

  auto.

  simpl in |- *; elim (varlist_lt v v0); simpl in |- *.
  repeat rewrite iacs_aux_ok.
  rewrite H; simpl in |- *; auto.

  simpl in H0.
  repeat rewrite iacs_aux_ok.
  rewrite H0. simpl in |- *; auto.
Qed.

Lemma abstract_sum_scalar_ok :
 forall (l:varlist) (s:abstract_sum),
   interp_acs (abstract_sum_scalar l s) =
   Amult (interp_vl Amult Aone Azero vm l) (interp_acs s).
Proof.
  simple induction s.
  simpl in |- *; eauto.

  simpl in |- *; intros.
  rewrite iacs_aux_ok.
  rewrite abstract_varlist_insert_ok.
  rewrite H.
  rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  auto.
Qed.

Lemma abstract_sum_prod_ok :
 forall x y:abstract_sum,
   interp_acs (abstract_sum_prod x y) = Amult (interp_acs x) (interp_acs y).

Proof.
  simple induction x.
  intros; simpl in |- *; eauto.

  destruct y as [| v0 a0]; intros.

  simpl in |- *; rewrite H; eauto.

  unfold abstract_sum_prod in |- *; fold abstract_sum_prod in |- *.
  rewrite abstract_sum_merge_ok.
  rewrite abstract_sum_scalar_ok.
  rewrite H; simpl in |- *; auto.
Qed.

Theorem aspolynomial_normalize_ok :
 forall x:aspolynomial, interp_asp x = interp_acs (aspolynomial_normalize x).
Proof.
  simple induction x; simpl in |- *; intros; trivial.
  rewrite abstract_sum_merge_ok.
  rewrite H; rewrite H0; eauto.
  rewrite abstract_sum_prod_ok.
  rewrite H; rewrite H0; eauto.
Qed.

End abstract_semi_rings.

Section abstract_rings.

(* In abstract polynomials there is no constants other
   than 0 and 1. An abstract ring is a ring whose operations plus,
   and mult are not functions but  constructors. In other words,
   when c1 and c2 are closed,  (plus c1 c2) doesn't reduce to a closed
   term. "closed" mean here "without plus and mult". *)

(* this section is not parametrized by a (semi-)ring.
   Nevertheless, they are two different types for semi-rings and rings
   and there will be 2 correction theorems *)

Inductive apolynomial : Type :=
  | APvar : index -> apolynomial
  | AP0 : apolynomial
  | AP1 : apolynomial
  | APplus : apolynomial -> apolynomial -> apolynomial
  | APmult : apolynomial -> apolynomial -> apolynomial
  | APopp : apolynomial -> apolynomial.

(* A canonical "abstract" sum is a list of varlist with the sign "+" or "-".
   Invariant : the list is sorted and there is no varlist is present
   with both signs. +x +x +x -x is forbidden => the canonical form is +x+x *)

Inductive signed_sum : Type :=
  | Nil_varlist : signed_sum
  | Plus_varlist : varlist -> signed_sum -> signed_sum
  | Minus_varlist : varlist -> signed_sum -> signed_sum.

Fixpoint signed_sum_merge (s1:signed_sum) : signed_sum -> signed_sum :=
  match s1 with
  | Plus_varlist l1 t1 =>
      (fix ssm_aux (s2:signed_sum) : signed_sum :=
         match s2 with
         | Plus_varlist l2 t2 =>
             if varlist_lt l1 l2
             then Plus_varlist l1 (signed_sum_merge t1 s2)
             else Plus_varlist l2 (ssm_aux t2)
         | Minus_varlist l2 t2 =>
             if varlist_eq l1 l2
             then signed_sum_merge t1 t2
             else
              if varlist_lt l1 l2
              then Plus_varlist l1 (signed_sum_merge t1 s2)
              else Minus_varlist l2 (ssm_aux t2)
         | Nil_varlist => s1
         end)
  | Minus_varlist l1 t1 =>
      (fix ssm_aux2 (s2:signed_sum) : signed_sum :=
         match s2 with
         | Plus_varlist l2 t2 =>
             if varlist_eq l1 l2
             then signed_sum_merge t1 t2
             else
              if varlist_lt l1 l2
              then Minus_varlist l1 (signed_sum_merge t1 s2)
              else Plus_varlist l2 (ssm_aux2 t2)
         | Minus_varlist l2 t2 =>
             if varlist_lt l1 l2
             then Minus_varlist l1 (signed_sum_merge t1 s2)
             else Minus_varlist l2 (ssm_aux2 t2)
         | Nil_varlist => s1
         end)
  | Nil_varlist => fun s2 => s2
  end.

Fixpoint plus_varlist_insert (l1:varlist) (s2:signed_sum) {struct s2} :
 signed_sum :=
  match s2 with
  | Plus_varlist l2 t2 =>
      if varlist_lt l1 l2
      then Plus_varlist l1 s2
      else Plus_varlist l2 (plus_varlist_insert l1 t2)
  | Minus_varlist l2 t2 =>
      if varlist_eq l1 l2
      then t2
      else
       if varlist_lt l1 l2
       then Plus_varlist l1 s2
       else Minus_varlist l2 (plus_varlist_insert l1 t2)
  | Nil_varlist => Plus_varlist l1 Nil_varlist
  end.

Fixpoint minus_varlist_insert (l1:varlist) (s2:signed_sum) {struct s2} :
 signed_sum :=
  match s2 with
  | Plus_varlist l2 t2 =>
      if varlist_eq l1 l2
      then t2
      else
       if varlist_lt l1 l2
       then Minus_varlist l1 s2
       else Plus_varlist l2 (minus_varlist_insert l1 t2)
  | Minus_varlist l2 t2 =>
      if varlist_lt l1 l2
      then Minus_varlist l1 s2
      else Minus_varlist l2 (minus_varlist_insert l1 t2)
  | Nil_varlist => Minus_varlist l1 Nil_varlist
  end.

Fixpoint signed_sum_opp (s:signed_sum) : signed_sum :=
  match s with
  | Plus_varlist l2 t2 => Minus_varlist l2 (signed_sum_opp t2)
  | Minus_varlist l2 t2 => Plus_varlist l2 (signed_sum_opp t2)
  | Nil_varlist => Nil_varlist
  end.


Fixpoint plus_sum_scalar (l1:varlist) (s2:signed_sum) {struct s2} :
 signed_sum :=
  match s2 with
  | Plus_varlist l2 t2 =>
      plus_varlist_insert (varlist_merge l1 l2) (plus_sum_scalar l1 t2)
  | Minus_varlist l2 t2 =>
      minus_varlist_insert (varlist_merge l1 l2) (plus_sum_scalar l1 t2)
  | Nil_varlist => Nil_varlist
  end.

Fixpoint minus_sum_scalar (l1:varlist) (s2:signed_sum) {struct s2} :
 signed_sum :=
  match s2 with
  | Plus_varlist l2 t2 =>
      minus_varlist_insert (varlist_merge l1 l2) (minus_sum_scalar l1 t2)
  | Minus_varlist l2 t2 =>
      plus_varlist_insert (varlist_merge l1 l2) (minus_sum_scalar l1 t2)
  | Nil_varlist => Nil_varlist
  end.

Fixpoint signed_sum_prod (s1 s2:signed_sum) {struct s1} : signed_sum :=
  match s1 with
  | Plus_varlist l1 t1 =>
      signed_sum_merge (plus_sum_scalar l1 s2) (signed_sum_prod t1 s2)
  | Minus_varlist l1 t1 =>
      signed_sum_merge (minus_sum_scalar l1 s2) (signed_sum_prod t1 s2)
  | Nil_varlist => Nil_varlist
  end.

Fixpoint apolynomial_normalize (p:apolynomial) : signed_sum :=
  match p with
  | APvar i => Plus_varlist (Cons_var i Nil_var) Nil_varlist
  | AP1 => Plus_varlist Nil_var Nil_varlist
  | AP0 => Nil_varlist
  | APplus l r =>
      signed_sum_merge (apolynomial_normalize l) (apolynomial_normalize r)
  | APmult l r =>
      signed_sum_prod (apolynomial_normalize l) (apolynomial_normalize r)
  | APopp q => signed_sum_opp (apolynomial_normalize q)
  end.


Variable A : Type.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp : A -> A.
Variable Aeq : A -> A -> bool.
Variable vm : varmap A.
Variable T : Ring_Theory Aplus Amult Aone Azero Aopp Aeq.

(* Local *) Definition isacs_aux :=
              (fix isacs_aux (a:A) (s:signed_sum) {struct s} : A :=
                 match s with
                 | Nil_varlist => a
                 | Plus_varlist l t =>
                     Aplus a (isacs_aux (interp_vl Amult Aone Azero vm l) t)
                 | Minus_varlist l t =>
                     Aplus a
                       (isacs_aux (Aopp (interp_vl Amult Aone Azero vm l)) t)
                 end).

Definition interp_sacs (s:signed_sum) : A :=
  match s with
  | Plus_varlist l t => isacs_aux (interp_vl Amult Aone Azero vm l) t
  | Minus_varlist l t => isacs_aux (Aopp (interp_vl Amult Aone Azero vm l)) t
  | Nil_varlist => Azero
  end.

Fixpoint interp_ap (p:apolynomial) : A :=
  match p with
  | APvar i => interp_var Azero vm i
  | AP0 => Azero
  | AP1 => Aone
  | APplus l r => Aplus (interp_ap l) (interp_ap r)
  | APmult l r => Amult (interp_ap l) (interp_ap r)
  | APopp q => Aopp (interp_ap q)
  end.

Hint Resolve (Th_plus_comm T).
Hint Resolve (Th_plus_assoc T).
Hint Resolve (Th_plus_assoc2 T).
Hint Resolve (Th_mult_comm T).
Hint Resolve (Th_mult_assoc T).
Hint Resolve (Th_mult_assoc2 T).
Hint Resolve (Th_plus_zero_left T).
Hint Resolve (Th_plus_zero_left2 T).
Hint Resolve (Th_mult_one_left T).
Hint Resolve (Th_mult_one_left2 T).
Hint Resolve (Th_mult_zero_left T).
Hint Resolve (Th_mult_zero_left2 T).
Hint Resolve (Th_distr_left T).
Hint Resolve (Th_distr_left2 T).
(*Hint Resolve (Th_plus_reg_left T).*)
Hint Resolve (Th_plus_permute T).
Hint Resolve (Th_mult_permute T).
Hint Resolve (Th_distr_right T).
Hint Resolve (Th_distr_right2 T).
Hint Resolve (Th_mult_zero_right2 T).
Hint Resolve (Th_plus_zero_right T).
Hint Resolve (Th_plus_zero_right2 T).
Hint Resolve (Th_mult_one_right T).
Hint Resolve (Th_mult_one_right2 T).
(*Hint Resolve (Th_plus_reg_right T).*)
Hint Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
Hint Immediate T.

Lemma isacs_aux_ok :
 forall (x:A) (s:signed_sum), isacs_aux x s = Aplus x (interp_sacs s).
Proof.
  simple induction s; simpl in |- *; intros.
  trivial.
  reflexivity.
  reflexivity.
Qed.

Hint Extern 10 (_ = _ :>A) => rewrite isacs_aux_ok: core.

Ltac solve1 v v0 H H0 :=
  simpl in |- *; elim (varlist_lt v v0); simpl in |- *; rewrite isacs_aux_ok;
   [ rewrite H; simpl in |- *; auto | simpl in H0; rewrite H0; auto ].

Lemma signed_sum_merge_ok :
 forall x y:signed_sum,
   interp_sacs (signed_sum_merge x y) = Aplus (interp_sacs x) (interp_sacs y).

  simple induction x.
  intro; simpl in |- *; auto.

  simple induction y; intros.

  auto.

  solve1 v v0 H H0.

  simpl in |- *; generalize (varlist_eq_prop v v0).
  elim (varlist_eq v v0); simpl in |- *.

  intro Heq; rewrite (Heq I).
  rewrite H.
  repeat rewrite isacs_aux_ok.
  rewrite (Th_plus_permute T).
  repeat rewrite (Th_plus_assoc T).
  rewrite
   (Th_plus_comm T (Aopp (interp_vl Amult Aone Azero vm v0))
      (interp_vl Amult Aone Azero vm v0)).
  rewrite (Th_opp_def T).
  rewrite (Th_plus_zero_left T).
  reflexivity.

  solve1 v v0 H H0.

  simple induction y; intros.

  auto.

  simpl in |- *; generalize (varlist_eq_prop v v0).
  elim (varlist_eq v v0); simpl in |- *.

  intro Heq; rewrite (Heq I).
  rewrite H.
  repeat rewrite isacs_aux_ok.
  rewrite (Th_plus_permute T).
  repeat rewrite (Th_plus_assoc T).
  rewrite (Th_opp_def T).
  rewrite (Th_plus_zero_left T).
  reflexivity.

  solve1 v v0 H H0.

  solve1 v v0 H H0.

Qed.

Ltac solve2 l v H :=
  elim (varlist_lt l v); simpl in |- *; rewrite isacs_aux_ok;
   [ auto | rewrite H; auto ].

Lemma plus_varlist_insert_ok :
 forall (l:varlist) (s:signed_sum),
   interp_sacs (plus_varlist_insert l s) =
   Aplus (interp_vl Amult Aone Azero vm l) (interp_sacs s).
Proof.

  simple induction s.
  trivial.

  simpl in |- *; intros.
  solve2 l v H.

  simpl in |- *; intros.
  generalize (varlist_eq_prop l v).
  elim (varlist_eq l v); simpl in |- *.

  intro Heq; rewrite (Heq I).
  repeat rewrite isacs_aux_ok.
  repeat rewrite (Th_plus_assoc T).
  rewrite (Th_opp_def T).
  rewrite (Th_plus_zero_left T).
  reflexivity.

  solve2 l v H.

Qed.

Lemma minus_varlist_insert_ok :
 forall (l:varlist) (s:signed_sum),
   interp_sacs (minus_varlist_insert l s) =
   Aplus (Aopp (interp_vl Amult Aone Azero vm l)) (interp_sacs s).
Proof.

  simple induction s.
  trivial.

  simpl in |- *; intros.
  generalize (varlist_eq_prop l v).
  elim (varlist_eq l v); simpl in |- *.

  intro Heq; rewrite (Heq I).
  repeat rewrite isacs_aux_ok.
  repeat rewrite (Th_plus_assoc T).
  rewrite
   (Th_plus_comm T (Aopp (interp_vl Amult Aone Azero vm v))
      (interp_vl Amult Aone Azero vm v)).
  rewrite (Th_opp_def T).
  auto.

  simpl in |- *; intros.
  solve2 l v H.

  simpl in |- *; intros; solve2 l v H.

Qed.

Lemma signed_sum_opp_ok :
 forall s:signed_sum, interp_sacs (signed_sum_opp s) = Aopp (interp_sacs s).
Proof.

  simple induction s; simpl in |- *; intros.

  symmetry  in |- *; apply (Th_opp_zero T).

  repeat rewrite isacs_aux_ok.
  rewrite H.
  rewrite (Th_plus_opp_opp T).
  reflexivity.

  repeat rewrite isacs_aux_ok.
  rewrite H.
  rewrite <- (Th_plus_opp_opp T).
  rewrite (Th_opp_opp T).
  reflexivity.

Qed.

Lemma plus_sum_scalar_ok :
 forall (l:varlist) (s:signed_sum),
   interp_sacs (plus_sum_scalar l s) =
   Amult (interp_vl Amult Aone Azero vm l) (interp_sacs s).
Proof.

  simple induction s.
  trivial.

  simpl in |- *; intros.
  rewrite plus_varlist_insert_ok.
  rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  repeat rewrite isacs_aux_ok.
  rewrite H.
  auto.

  simpl in |- *; intros.
  rewrite minus_varlist_insert_ok.
  repeat rewrite isacs_aux_ok.
  rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  rewrite H.
  rewrite (Th_distr_right T).
  rewrite <- (Th_opp_mult_right T).
  reflexivity.

Qed.

Lemma minus_sum_scalar_ok :
 forall (l:varlist) (s:signed_sum),
   interp_sacs (minus_sum_scalar l s) =
   Aopp (Amult (interp_vl Amult Aone Azero vm l) (interp_sacs s)).
Proof.

  simple induction s; simpl in |- *; intros.

  rewrite (Th_mult_zero_right T); symmetry  in |- *; apply (Th_opp_zero T).

  simpl in |- *; intros.
  rewrite minus_varlist_insert_ok.
  rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  repeat rewrite isacs_aux_ok.
  rewrite H.
  rewrite (Th_distr_right T).
  rewrite (Th_plus_opp_opp T).
  reflexivity.

  simpl in |- *; intros.
  rewrite plus_varlist_insert_ok.
  repeat rewrite isacs_aux_ok.
  rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  rewrite H.
  rewrite (Th_distr_right T).
  rewrite <- (Th_opp_mult_right T).
  rewrite <- (Th_plus_opp_opp T).
  rewrite (Th_opp_opp T).
  reflexivity.

Qed.

Lemma signed_sum_prod_ok :
 forall x y:signed_sum,
   interp_sacs (signed_sum_prod x y) = Amult (interp_sacs x) (interp_sacs y).
Proof.

  simple induction x.

  simpl in |- *; eauto 1.

  intros; simpl in |- *.
  rewrite signed_sum_merge_ok.
  rewrite plus_sum_scalar_ok.
  repeat rewrite isacs_aux_ok.
  rewrite H.
  auto.

  intros; simpl in |- *.
  repeat rewrite isacs_aux_ok.
  rewrite signed_sum_merge_ok.
  rewrite minus_sum_scalar_ok.
  rewrite H.
  rewrite (Th_distr_left T).
  rewrite (Th_opp_mult_left T).
  reflexivity.

Qed.

Theorem apolynomial_normalize_ok :
 forall p:apolynomial, interp_sacs (apolynomial_normalize p) = interp_ap p.
Proof.
  simple induction p; simpl in |- *; auto 1.
  intros.
    rewrite signed_sum_merge_ok.
    rewrite H; rewrite H0; reflexivity.
  intros.
    rewrite signed_sum_prod_ok.
    rewrite H; rewrite H0; reflexivity.
  intros.
    rewrite signed_sum_opp_ok.
    rewrite H; reflexivity.
Qed.

End abstract_rings.
