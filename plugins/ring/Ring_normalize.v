(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Import LegacyRing_theory.
Require Import Quote.

Set Implicit Arguments.
Unset Boxed Definitions.

Lemma index_eq_prop : forall n m:index, Is_true (index_eq n m) -> n = m.
Proof.
  intros.
  apply index_eq_prop.
  generalize H.
  case (index_eq n m); simpl in |- *; trivial; intros.
  contradiction.
Qed.

Section semi_rings.

Variable A : Type.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aeq : A -> A -> bool.

(* Section definitions. *)


(******************************************)
(* Normal abtract Polynomials             *)
(******************************************)
(* DEFINITIONS :
- A varlist is a sorted product of one or more variables : x, x*y*z
- A monom is a constant, a varlist or the product of a constant by a varlist
  variables. 2*x*y, x*y*z, 3 are monoms : 2*3, x*3*y, 4*x*3 are NOT.
- A canonical sum is either a monom or an ordered sum of monoms
  (the order on monoms is defined later)
- A normal polynomial it either a constant or a canonical sum or a constant
  plus a canonical sum
*)

(* varlist is isomorphic to (list var), but we built a special inductive
   for efficiency *)
Inductive varlist : Type :=
  | Nil_var : varlist
  | Cons_var : index -> varlist -> varlist.

Inductive canonical_sum : Type :=
  | Nil_monom : canonical_sum
  | Cons_monom : A -> varlist -> canonical_sum -> canonical_sum
  | Cons_varlist : varlist -> canonical_sum -> canonical_sum.

(* Order on monoms *)

(* That's the lexicographic order on varlist, extended by :
  - A constant is less than every monom
  - The relation between two varlist is preserved by multiplication by a
  constant.

  Examples :
  3 < x < y
  x*y < x*y*y*z
  2*x*y < x*y*y*z
  x*y < 54*x*y*y*z
  4*x*y < 59*x*y*y*z
*)

Fixpoint varlist_eq (x y:varlist) {struct y} : bool :=
  match x, y with
  | Nil_var, Nil_var => true
  | Cons_var i xrest, Cons_var j yrest =>
      andb (index_eq i j) (varlist_eq xrest yrest)
  | _, _ => false
  end.

Fixpoint varlist_lt (x y:varlist) {struct y} : bool :=
  match x, y with
  | Nil_var, Cons_var _ _ => true
  | Cons_var i xrest, Cons_var j yrest =>
      if index_lt i j
      then true
      else andb (index_eq i j) (varlist_lt xrest yrest)
  | _, _ => false
  end.

(* merges two variables lists *)
Fixpoint varlist_merge (l1:varlist) : varlist -> varlist :=
  match l1 with
  | Cons_var v1 t1 =>
      (fix vm_aux (l2:varlist) : varlist :=
         match l2 with
         | Cons_var v2 t2 =>
             if index_lt v1 v2
             then Cons_var v1 (varlist_merge t1 l2)
             else Cons_var v2 (vm_aux t2)
         | Nil_var => l1
         end)
  | Nil_var => fun l2 => l2
  end.

(* returns the sum of two canonical sums  *)
Fixpoint canonical_sum_merge (s1:canonical_sum) :
 canonical_sum -> canonical_sum :=
  match s1 with
  | Cons_monom c1 l1 t1 =>
      (fix csm_aux (s2:canonical_sum) : canonical_sum :=
         match s2 with
         | Cons_monom c2 l2 t2 =>
             if varlist_eq l1 l2
             then Cons_monom (Aplus c1 c2) l1 (canonical_sum_merge t1 t2)
             else
              if varlist_lt l1 l2
              then Cons_monom c1 l1 (canonical_sum_merge t1 s2)
              else Cons_monom c2 l2 (csm_aux t2)
         | Cons_varlist l2 t2 =>
             if varlist_eq l1 l2
             then Cons_monom (Aplus c1 Aone) l1 (canonical_sum_merge t1 t2)
             else
              if varlist_lt l1 l2
              then Cons_monom c1 l1 (canonical_sum_merge t1 s2)
              else Cons_varlist l2 (csm_aux t2)
         | Nil_monom => s1
         end)
  | Cons_varlist l1 t1 =>
      (fix csm_aux2 (s2:canonical_sum) : canonical_sum :=
         match s2 with
         | Cons_monom c2 l2 t2 =>
             if varlist_eq l1 l2
             then Cons_monom (Aplus Aone c2) l1 (canonical_sum_merge t1 t2)
             else
              if varlist_lt l1 l2
              then Cons_varlist l1 (canonical_sum_merge t1 s2)
              else Cons_monom c2 l2 (csm_aux2 t2)
         | Cons_varlist l2 t2 =>
             if varlist_eq l1 l2
             then Cons_monom (Aplus Aone Aone) l1 (canonical_sum_merge t1 t2)
             else
              if varlist_lt l1 l2
              then Cons_varlist l1 (canonical_sum_merge t1 s2)
              else Cons_varlist l2 (csm_aux2 t2)
         | Nil_monom => s1
         end)
  | Nil_monom => fun s2 => s2
  end.

(* Insertion of a monom in a canonical sum *)
Fixpoint monom_insert (c1:A) (l1:varlist) (s2:canonical_sum) {struct s2} :
 canonical_sum :=
  match s2 with
  | Cons_monom c2 l2 t2 =>
      if varlist_eq l1 l2
      then Cons_monom (Aplus c1 c2) l1 t2
      else
       if varlist_lt l1 l2
       then Cons_monom c1 l1 s2
       else Cons_monom c2 l2 (monom_insert c1 l1 t2)
  | Cons_varlist l2 t2 =>
      if varlist_eq l1 l2
      then Cons_monom (Aplus c1 Aone) l1 t2
      else
       if varlist_lt l1 l2
       then Cons_monom c1 l1 s2
       else Cons_varlist l2 (monom_insert c1 l1 t2)
  | Nil_monom => Cons_monom c1 l1 Nil_monom
  end.

Fixpoint varlist_insert (l1:varlist) (s2:canonical_sum) {struct s2} :
 canonical_sum :=
  match s2 with
  | Cons_monom c2 l2 t2 =>
      if varlist_eq l1 l2
      then Cons_monom (Aplus Aone c2) l1 t2
      else
       if varlist_lt l1 l2
       then Cons_varlist l1 s2
       else Cons_monom c2 l2 (varlist_insert l1 t2)
  | Cons_varlist l2 t2 =>
      if varlist_eq l1 l2
      then Cons_monom (Aplus Aone Aone) l1 t2
      else
       if varlist_lt l1 l2
       then Cons_varlist l1 s2
       else Cons_varlist l2 (varlist_insert l1 t2)
  | Nil_monom => Cons_varlist l1 Nil_monom
  end.

(* Computes c0*s *)
Fixpoint canonical_sum_scalar (c0:A) (s:canonical_sum) {struct s} :
 canonical_sum :=
  match s with
  | Cons_monom c l t => Cons_monom (Amult c0 c) l (canonical_sum_scalar c0 t)
  | Cons_varlist l t => Cons_monom c0 l (canonical_sum_scalar c0 t)
  | Nil_monom => Nil_monom
  end.

(* Computes l0*s  *)
Fixpoint canonical_sum_scalar2 (l0:varlist) (s:canonical_sum) {struct s} :
 canonical_sum :=
  match s with
  | Cons_monom c l t =>
      monom_insert c (varlist_merge l0 l) (canonical_sum_scalar2 l0 t)
  | Cons_varlist l t =>
      varlist_insert (varlist_merge l0 l) (canonical_sum_scalar2 l0 t)
  | Nil_monom => Nil_monom
  end.

(* Computes c0*l0*s  *)
Fixpoint canonical_sum_scalar3 (c0:A) (l0:varlist)
 (s:canonical_sum) {struct s} : canonical_sum :=
  match s with
  | Cons_monom c l t =>
      monom_insert (Amult c0 c) (varlist_merge l0 l)
        (canonical_sum_scalar3 c0 l0 t)
  | Cons_varlist l t =>
      monom_insert c0 (varlist_merge l0 l) (canonical_sum_scalar3 c0 l0 t)
  | Nil_monom => Nil_monom
  end.

(* returns the product of two canonical sums *)
Fixpoint canonical_sum_prod (s1 s2:canonical_sum) {struct s1} :
 canonical_sum :=
  match s1 with
  | Cons_monom c1 l1 t1 =>
      canonical_sum_merge (canonical_sum_scalar3 c1 l1 s2)
        (canonical_sum_prod t1 s2)
  | Cons_varlist l1 t1 =>
      canonical_sum_merge (canonical_sum_scalar2 l1 s2)
        (canonical_sum_prod t1 s2)
  | Nil_monom => Nil_monom
  end.

(* The type to represent concrete semi-ring polynomials *)
Inductive spolynomial : Type :=
  | SPvar : index -> spolynomial
  | SPconst : A -> spolynomial
  | SPplus : spolynomial -> spolynomial -> spolynomial
  | SPmult : spolynomial -> spolynomial -> spolynomial.

Fixpoint spolynomial_normalize (p:spolynomial) : canonical_sum :=
  match p with
  | SPvar i => Cons_varlist (Cons_var i Nil_var) Nil_monom
  | SPconst c => Cons_monom c Nil_var Nil_monom
  | SPplus l r =>
      canonical_sum_merge (spolynomial_normalize l) (spolynomial_normalize r)
  | SPmult l r =>
      canonical_sum_prod (spolynomial_normalize l) (spolynomial_normalize r)
  end.

(* Deletion of useless 0 and 1 in canonical sums *)
Fixpoint canonical_sum_simplify (s:canonical_sum) : canonical_sum :=
  match s with
  | Cons_monom c l t =>
      if Aeq c Azero
      then canonical_sum_simplify t
      else
       if Aeq c Aone
       then Cons_varlist l (canonical_sum_simplify t)
       else Cons_monom c l (canonical_sum_simplify t)
  | Cons_varlist l t => Cons_varlist l (canonical_sum_simplify t)
  | Nil_monom => Nil_monom
  end.

Definition spolynomial_simplify (x:spolynomial) :=
  canonical_sum_simplify (spolynomial_normalize x).

(* End definitions. *)

(* Section interpretation. *)

(*** Here a variable map is defined and the interpetation of a spolynom
  acording to a certain variables map. Once again the choosen definition
  is generic and could be changed ****)

Variable vm : varmap A.

(* Interpretation of list of variables
 * [x1; ... ; xn ] is interpreted as (find v x1)* ... *(find v xn)
 * The unbound variables are mapped to 0. Normally this case sould
 * never occur. Since we want only to prove correctness theorems, which form
 * is : for any varmap and any spolynom ... this is a safe and pain-saving
 * choice *)
Definition interp_var (i:index) := varmap_find Azero i vm.

(* Local *) Definition ivl_aux :=
              (fix ivl_aux (x:index) (t:varlist) {struct t} : A :=
                 match t with
                 | Nil_var => interp_var x
                 | Cons_var x' t' => Amult (interp_var x) (ivl_aux x' t')
                 end).

Definition interp_vl (l:varlist) :=
  match l with
  | Nil_var => Aone
  | Cons_var x t => ivl_aux x t
  end.

(* Local *) Definition interp_m (c:A) (l:varlist) :=
              match l with
              | Nil_var => c
              | Cons_var x t => Amult c (ivl_aux x t)
              end.

(* Local *) Definition ics_aux :=
              (fix ics_aux (a:A) (s:canonical_sum) {struct s} : A :=
                 match s with
                 | Nil_monom => a
                 | Cons_varlist l t => Aplus a (ics_aux (interp_vl l) t)
                 | Cons_monom c l t => Aplus a (ics_aux (interp_m c l) t)
                 end).

(* Interpretation of a canonical sum *)
Definition interp_cs (s:canonical_sum) : A :=
  match s with
  | Nil_monom => Azero
  | Cons_varlist l t => ics_aux (interp_vl l) t
  | Cons_monom c l t => ics_aux (interp_m c l) t
  end.

Fixpoint interp_sp (p:spolynomial) : A :=
  match p with
  | SPconst c => c
  | SPvar i => interp_var i
  | SPplus p1 p2 => Aplus (interp_sp p1) (interp_sp p2)
  | SPmult p1 p2 => Amult (interp_sp p1) (interp_sp p2)
  end.


(* End interpretation. *)

Unset Implicit Arguments.

(* Section properties. *)

Variable T : Semi_Ring_Theory Aplus Amult Aone Azero Aeq.

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
(* Hints Resolve refl_eqT sym_eqT trans_eqT. *)
Hint Immediate T.

Lemma varlist_eq_prop : forall x y:varlist, Is_true (varlist_eq x y) -> x = y.
Proof.
  simple induction x; simple induction y; contradiction || (try reflexivity).
  simpl in |- *; intros.
  generalize (andb_prop2 _ _ H1); intros; elim H2; intros.
  rewrite (index_eq_prop _ _ H3); rewrite (H v0 H4); reflexivity.
Qed.

Remark ivl_aux_ok :
 forall (v:varlist) (i:index),
   ivl_aux i v = Amult (interp_var i) (interp_vl v).
Proof.
  simple induction v; simpl in |- *; intros.
  trivial.
  rewrite H; trivial.
Qed.

Lemma varlist_merge_ok :
 forall x y:varlist,
   interp_vl (varlist_merge x y) = Amult (interp_vl x) (interp_vl y).
Proof.
  simple induction x.
  simpl in |- *; trivial.
  simple induction y.
  simpl in |- *; trivial.
  simpl in |- *; intros.
  elim (index_lt i i0); simpl in |- *; intros.

  repeat rewrite ivl_aux_ok.
  rewrite H. simpl in |- *.
  rewrite ivl_aux_ok.
  eauto.

  repeat rewrite ivl_aux_ok.
  rewrite H0.
  rewrite ivl_aux_ok.
  eauto.
Qed.

Remark ics_aux_ok :
 forall (x:A) (s:canonical_sum), ics_aux x s = Aplus x (interp_cs s).
Proof.
  simple induction s; simpl in |- *; intros.
  trivial.
  reflexivity.
  reflexivity.
Qed.

Remark interp_m_ok :
 forall (x:A) (l:varlist), interp_m x l = Amult x (interp_vl l).
Proof.
  destruct l as [| i v].
  simpl in |- *; trivial.
  reflexivity.
Qed.

Lemma canonical_sum_merge_ok :
 forall x y:canonical_sum,
   interp_cs (canonical_sum_merge x y) = Aplus (interp_cs x) (interp_cs y).

simple induction x; simpl in |- *.
trivial.

simple induction y; simpl in |- *; intros.
(* monom and nil *)
eauto.

(* monom and monom *)
generalize (varlist_eq_prop v v0).
elim (varlist_eq v v0).
intros; rewrite (H1 I).
simpl in |- *; repeat rewrite ics_aux_ok; rewrite H.
repeat rewrite interp_m_ok.
rewrite (SR_distr_left T).
repeat rewrite <- (SR_plus_assoc T).
apply f_equal with (f := Aplus (Amult a (interp_vl v0))).
trivial.

elim (varlist_lt v v0); simpl in |- *.
repeat rewrite ics_aux_ok.
rewrite H; simpl in |- *; rewrite ics_aux_ok; eauto.

rewrite ics_aux_ok; rewrite H0; repeat rewrite ics_aux_ok; simpl in |- *;
 eauto.

(* monom and varlist *)
generalize (varlist_eq_prop v v0).
elim (varlist_eq v v0).
intros; rewrite (H1 I).
simpl in |- *; repeat rewrite ics_aux_ok; rewrite H.
repeat rewrite interp_m_ok.
rewrite (SR_distr_left T).
repeat rewrite <- (SR_plus_assoc T).
apply f_equal with (f := Aplus (Amult a (interp_vl v0))).
rewrite (SR_mult_one_left T).
trivial.

elim (varlist_lt v v0); simpl in |- *.
repeat rewrite ics_aux_ok.
rewrite H; simpl in |- *; rewrite ics_aux_ok; eauto.
rewrite ics_aux_ok; rewrite H0; repeat rewrite ics_aux_ok; simpl in |- *;
 eauto.

simple induction y; simpl in |- *; intros.
(* varlist and nil *)
trivial.

(* varlist and monom *)
generalize (varlist_eq_prop v v0).
elim (varlist_eq v v0).
intros; rewrite (H1 I).
simpl in |- *; repeat rewrite ics_aux_ok; rewrite H.
repeat rewrite interp_m_ok.
rewrite (SR_distr_left T).
repeat rewrite <- (SR_plus_assoc T).
rewrite (SR_mult_one_left T).
apply f_equal with (f := Aplus (interp_vl v0)).
trivial.

elim (varlist_lt v v0); simpl in |- *.
repeat rewrite ics_aux_ok.
rewrite H; simpl in |- *; rewrite ics_aux_ok; eauto.
rewrite ics_aux_ok; rewrite H0; repeat rewrite ics_aux_ok; simpl in |- *;
 eauto.

(* varlist and varlist *)
generalize (varlist_eq_prop v v0).
elim (varlist_eq v v0).
intros; rewrite (H1 I).
simpl in |- *; repeat rewrite ics_aux_ok; rewrite H.
repeat rewrite interp_m_ok.
rewrite (SR_distr_left T).
repeat rewrite <- (SR_plus_assoc T).
rewrite (SR_mult_one_left T).
apply f_equal with (f := Aplus (interp_vl v0)).
trivial.

elim (varlist_lt v v0); simpl in |- *.
repeat rewrite ics_aux_ok.
rewrite H; simpl in |- *; rewrite ics_aux_ok; eauto.
rewrite ics_aux_ok; rewrite H0; repeat rewrite ics_aux_ok; simpl in |- *;
 eauto.
Qed.

Lemma monom_insert_ok :
 forall (a:A) (l:varlist) (s:canonical_sum),
   interp_cs (monom_insert a l s) =
   Aplus (Amult a (interp_vl l)) (interp_cs s).
intros; generalize s; simple induction s0.

simpl in |- *; rewrite interp_m_ok; trivial.

simpl in |- *; intros.
generalize (varlist_eq_prop l v); elim (varlist_eq l v).
intro Hr; rewrite (Hr I); simpl in |- *; rewrite interp_m_ok;
 repeat rewrite ics_aux_ok; rewrite interp_m_ok; rewrite (SR_distr_left T);
 eauto.
elim (varlist_lt l v); simpl in |- *;
 [ repeat rewrite interp_m_ok; rewrite ics_aux_ok; eauto
 | repeat rewrite interp_m_ok; rewrite ics_aux_ok; rewrite H;
    rewrite ics_aux_ok; eauto ].

simpl in |- *; intros.
generalize (varlist_eq_prop l v); elim (varlist_eq l v).
intro Hr; rewrite (Hr I); simpl in |- *; rewrite interp_m_ok;
 repeat rewrite ics_aux_ok; rewrite (SR_distr_left T);
 rewrite (SR_mult_one_left T); eauto.
elim (varlist_lt l v); simpl in |- *;
 [ repeat rewrite interp_m_ok; rewrite ics_aux_ok; eauto
 | repeat rewrite interp_m_ok; rewrite ics_aux_ok; rewrite H;
    rewrite ics_aux_ok; eauto ].
Qed.

Lemma varlist_insert_ok :
 forall (l:varlist) (s:canonical_sum),
   interp_cs (varlist_insert l s) = Aplus (interp_vl l) (interp_cs s).
intros; generalize s; simple induction s0.

simpl in |- *; trivial.

simpl in |- *; intros.
generalize (varlist_eq_prop l v); elim (varlist_eq l v).
intro Hr; rewrite (Hr I); simpl in |- *; rewrite interp_m_ok;
 repeat rewrite ics_aux_ok; rewrite interp_m_ok; rewrite (SR_distr_left T);
 rewrite (SR_mult_one_left T); eauto.
elim (varlist_lt l v); simpl in |- *;
 [ repeat rewrite interp_m_ok; rewrite ics_aux_ok; eauto
 | repeat rewrite interp_m_ok; rewrite ics_aux_ok; rewrite H;
    rewrite ics_aux_ok; eauto ].

simpl in |- *; intros.
generalize (varlist_eq_prop l v); elim (varlist_eq l v).
intro Hr; rewrite (Hr I); simpl in |- *; rewrite interp_m_ok;
 repeat rewrite ics_aux_ok; rewrite (SR_distr_left T);
 rewrite (SR_mult_one_left T); eauto.
elim (varlist_lt l v); simpl in |- *;
 [ repeat rewrite interp_m_ok; rewrite ics_aux_ok; eauto
 | repeat rewrite interp_m_ok; rewrite ics_aux_ok; rewrite H;
    rewrite ics_aux_ok; eauto ].
Qed.

Lemma canonical_sum_scalar_ok :
 forall (a:A) (s:canonical_sum),
   interp_cs (canonical_sum_scalar a s) = Amult a (interp_cs s).
simple induction s.
simpl in |- *; eauto.

simpl in |- *; intros.
repeat rewrite ics_aux_ok.
repeat rewrite interp_m_ok.
rewrite H.
rewrite (SR_distr_right T).
repeat rewrite <- (SR_mult_assoc T).
reflexivity.

simpl in |- *; intros.
repeat rewrite ics_aux_ok.
repeat rewrite interp_m_ok.
rewrite H.
rewrite (SR_distr_right T).
repeat rewrite <- (SR_mult_assoc T).
reflexivity.
Qed.

Lemma canonical_sum_scalar2_ok :
 forall (l:varlist) (s:canonical_sum),
   interp_cs (canonical_sum_scalar2 l s) = Amult (interp_vl l) (interp_cs s).
simple induction s.
simpl in |- *; trivial.

simpl in |- *; intros.
rewrite monom_insert_ok.
repeat rewrite ics_aux_ok.
repeat rewrite interp_m_ok.
rewrite H.
rewrite varlist_merge_ok.
repeat rewrite (SR_distr_right T).
repeat rewrite <- (SR_mult_assoc T).
repeat rewrite <- (SR_plus_assoc T).
rewrite (SR_mult_permute T a (interp_vl l) (interp_vl v)).
reflexivity.

simpl in |- *; intros.
rewrite varlist_insert_ok.
repeat rewrite ics_aux_ok.
repeat rewrite interp_m_ok.
rewrite H.
rewrite varlist_merge_ok.
repeat rewrite (SR_distr_right T).
repeat rewrite <- (SR_mult_assoc T).
repeat rewrite <- (SR_plus_assoc T).
reflexivity.
Qed.

Lemma canonical_sum_scalar3_ok :
 forall (c:A) (l:varlist) (s:canonical_sum),
   interp_cs (canonical_sum_scalar3 c l s) =
   Amult c (Amult (interp_vl l) (interp_cs s)).
simple induction s.
simpl in |- *; repeat rewrite (SR_mult_zero_right T); reflexivity.

simpl in |- *; intros.
rewrite monom_insert_ok.
repeat rewrite ics_aux_ok.
repeat rewrite interp_m_ok.
rewrite H.
rewrite varlist_merge_ok.
repeat rewrite (SR_distr_right T).
repeat rewrite <- (SR_mult_assoc T).
repeat rewrite <- (SR_plus_assoc T).
rewrite (SR_mult_permute T a (interp_vl l) (interp_vl v)).
reflexivity.

simpl in |- *; intros.
rewrite monom_insert_ok.
repeat rewrite ics_aux_ok.
repeat rewrite interp_m_ok.
rewrite H.
rewrite varlist_merge_ok.
repeat rewrite (SR_distr_right T).
repeat rewrite <- (SR_mult_assoc T).
repeat rewrite <- (SR_plus_assoc T).
rewrite (SR_mult_permute T c (interp_vl l) (interp_vl v)).
reflexivity.
Qed.

Lemma canonical_sum_prod_ok :
 forall x y:canonical_sum,
   interp_cs (canonical_sum_prod x y) = Amult (interp_cs x) (interp_cs y).
simple induction x; simpl in |- *; intros.
trivial.

rewrite canonical_sum_merge_ok.
rewrite canonical_sum_scalar3_ok.
rewrite ics_aux_ok.
rewrite interp_m_ok.
rewrite H.
rewrite (SR_mult_assoc T a (interp_vl v) (interp_cs y)).
symmetry  in |- *.
eauto.

rewrite canonical_sum_merge_ok.
rewrite canonical_sum_scalar2_ok.
rewrite ics_aux_ok.
rewrite H.
trivial.
Qed.

Theorem spolynomial_normalize_ok :
 forall p:spolynomial, interp_cs (spolynomial_normalize p) = interp_sp p.
simple induction p; simpl in |- *; intros.

reflexivity.
reflexivity.

rewrite canonical_sum_merge_ok.
rewrite H; rewrite H0.
reflexivity.

rewrite canonical_sum_prod_ok.
rewrite H; rewrite H0.
reflexivity.
Qed.

Lemma canonical_sum_simplify_ok :
 forall s:canonical_sum, interp_cs (canonical_sum_simplify s) = interp_cs s.
simple induction s.

reflexivity.

(* cons_monom *)
simpl in |- *; intros.
generalize (SR_eq_prop T a Azero).
elim (Aeq a Azero).
intro Heq; rewrite (Heq I).
rewrite H.
rewrite ics_aux_ok.
rewrite interp_m_ok.
rewrite (SR_mult_zero_left T).
trivial.

intros; simpl in |- *.
generalize (SR_eq_prop T a Aone).
elim (Aeq a Aone).
intro Heq; rewrite (Heq I).
simpl in |- *.
repeat rewrite ics_aux_ok.
rewrite interp_m_ok.
rewrite H.
rewrite (SR_mult_one_left T).
reflexivity.

simpl in |- *.
repeat rewrite ics_aux_ok.
rewrite interp_m_ok.
rewrite H.
reflexivity.

(* cons_varlist *)
simpl in |- *; intros.
repeat rewrite ics_aux_ok.
rewrite H.
reflexivity.

Qed.

Theorem spolynomial_simplify_ok :
 forall p:spolynomial, interp_cs (spolynomial_simplify p) = interp_sp p.
intro.
unfold spolynomial_simplify in |- *.
rewrite canonical_sum_simplify_ok.
apply spolynomial_normalize_ok.
Qed.

(* End properties. *)
End semi_rings.

Implicit Arguments Cons_varlist.
Implicit Arguments Cons_monom.
Implicit Arguments SPconst.
Implicit Arguments SPplus.
Implicit Arguments SPmult.

Section rings.

(* Here the coercion between Ring and Semi-Ring will be useful *)

Set Implicit Arguments.

Variable A : Type.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp : A -> A.
Variable Aeq : A -> A -> bool.
Variable vm : varmap A.
Variable T : Ring_Theory Aplus Amult Aone Azero Aopp Aeq.

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
Hint Resolve (Th_mult_zero_right T).
Hint Resolve (Th_mult_zero_right2 T).
Hint Resolve (Th_plus_zero_right T).
Hint Resolve (Th_plus_zero_right2 T).
Hint Resolve (Th_mult_one_right T).
Hint Resolve (Th_mult_one_right2 T).
(*Hint Resolve (Th_plus_reg_right T).*)
Hint Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
Hint Immediate T.

(*** Definitions *)

Inductive polynomial : Type :=
  | Pvar : index -> polynomial
  | Pconst : A -> polynomial
  | Pplus : polynomial -> polynomial -> polynomial
  | Pmult : polynomial -> polynomial -> polynomial
  | Popp : polynomial -> polynomial.

Fixpoint polynomial_normalize (x:polynomial) : canonical_sum A :=
  match x with
  | Pplus l r =>
      canonical_sum_merge Aplus Aone (polynomial_normalize l)
        (polynomial_normalize r)
  | Pmult l r =>
      canonical_sum_prod Aplus Amult Aone (polynomial_normalize l)
        (polynomial_normalize r)
  | Pconst c => Cons_monom c Nil_var (Nil_monom A)
  | Pvar i => Cons_varlist (Cons_var i Nil_var) (Nil_monom A)
  | Popp p =>
      canonical_sum_scalar3 Aplus Amult Aone (Aopp Aone) Nil_var
        (polynomial_normalize p)
  end.

Definition polynomial_simplify (x:polynomial) :=
  canonical_sum_simplify Aone Azero Aeq (polynomial_normalize x).

Fixpoint spolynomial_of (x:polynomial) : spolynomial A :=
  match x with
  | Pplus l r => SPplus (spolynomial_of l) (spolynomial_of r)
  | Pmult l r => SPmult (spolynomial_of l) (spolynomial_of r)
  | Pconst c => SPconst c
  | Pvar i => SPvar A i
  | Popp p => SPmult (SPconst (Aopp Aone)) (spolynomial_of p)
  end.

(*** Interpretation *)

Fixpoint interp_p (p:polynomial) : A :=
  match p with
  | Pconst c => c
  | Pvar i => varmap_find Azero i vm
  | Pplus p1 p2 => Aplus (interp_p p1) (interp_p p2)
  | Pmult p1 p2 => Amult (interp_p p1) (interp_p p2)
  | Popp p1 => Aopp (interp_p p1)
  end.

(*** Properties *)

Unset Implicit Arguments.

Lemma spolynomial_of_ok :
 forall p:polynomial,
   interp_p p = interp_sp Aplus Amult Azero vm (spolynomial_of p).
simple induction p; reflexivity || (simpl in |- *; intros).
rewrite H; rewrite H0; reflexivity.
rewrite H; rewrite H0; reflexivity.
rewrite H.
rewrite (Th_opp_mult_left2 T).
rewrite (Th_mult_one_left T).
reflexivity.
Qed.

Theorem polynomial_normalize_ok :
 forall p:polynomial,
   polynomial_normalize p =
   spolynomial_normalize Aplus Amult Aone (spolynomial_of p).
simple induction p; reflexivity || (simpl in |- *; intros).
rewrite H; rewrite H0; reflexivity.
rewrite H; rewrite H0; reflexivity.
rewrite H; simpl in |- *.
elim
 (canonical_sum_scalar3 Aplus Amult Aone (Aopp Aone) Nil_var
    (spolynomial_normalize Aplus Amult Aone (spolynomial_of p0)));
 [ reflexivity
 | simpl in |- *; intros; rewrite H0; reflexivity
 | simpl in |- *; intros; rewrite H0; reflexivity ].
Qed.

Theorem polynomial_simplify_ok :
 forall p:polynomial,
   interp_cs Aplus Amult Aone Azero vm (polynomial_simplify p) = interp_p p.
intro.
unfold polynomial_simplify in |- *.
rewrite spolynomial_of_ok.
rewrite polynomial_normalize_ok.
rewrite (canonical_sum_simplify_ok A Aplus Amult Aone Azero Aeq vm T).
rewrite (spolynomial_normalize_ok A Aplus Amult Aone Azero Aeq vm T).
reflexivity.
Qed.

End rings.

Infix "+" := Pplus : ring_scope.
Infix "*" := Pmult : ring_scope.
Notation "- x" := (Popp x) : ring_scope.
Notation "[ x ]" := (Pvar x) (at level 0) : ring_scope.

Delimit Scope ring_scope with ring.
