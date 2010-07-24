(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Import Setoid_ring_theory.
Require Import Quote.

Set Implicit Arguments.
Unset Boxed Definitions.

Lemma index_eq_prop : forall n m:index, Is_true (index_eq n m) -> n = m.
Proof.
  simple induction n; simple induction m; simpl in |- *;
   try reflexivity || contradiction.
  intros; rewrite (H i0); trivial.
  intros; rewrite (H i0); trivial.
Qed.

Section setoid.

Variable A : Type.
Variable Aequiv : A -> A -> Prop.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp : A -> A.
Variable Aeq : A -> A -> bool.

Variable S : Setoid_Theory A Aequiv.

Add Setoid A Aequiv S as Asetoid.

Variable plus_morph :
 forall a a0:A, Aequiv a a0 ->
   forall a1 a2:A, Aequiv a1 a2 ->
     Aequiv (Aplus a a1)  (Aplus a0 a2).
Variable mult_morph :
 forall a a0:A, Aequiv a a0 ->
   forall a1 a2:A, Aequiv a1 a2 ->
     Aequiv (Amult a a1) (Amult a0 a2).
Variable opp_morph : forall a a0:A, Aequiv a a0 -> Aequiv (Aopp a) (Aopp a0).

Add Morphism Aplus : Aplus_ext.
intros; apply plus_morph; assumption.
Qed.

Add Morphism Amult : Amult_ext.
intros; apply mult_morph; assumption.
Qed.

Add Morphism Aopp : Aopp_ext.
exact opp_morph.
Qed.

Let equiv_refl := Seq_refl A Aequiv S.
Let equiv_sym := Seq_sym A Aequiv S.
Let equiv_trans := Seq_trans A Aequiv S.

Hint Resolve equiv_refl equiv_trans.
Hint Immediate equiv_sym.

Section semi_setoid_rings.

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

(* The type to represent concrete semi-setoid-ring polynomials *)

Inductive setspolynomial : Type :=
  | SetSPvar : index -> setspolynomial
  | SetSPconst : A -> setspolynomial
  | SetSPplus : setspolynomial -> setspolynomial -> setspolynomial
  | SetSPmult : setspolynomial -> setspolynomial -> setspolynomial.

Fixpoint setspolynomial_normalize (p:setspolynomial) : canonical_sum :=
  match p with
  | SetSPplus l r =>
      canonical_sum_merge (setspolynomial_normalize l)
        (setspolynomial_normalize r)
  | SetSPmult l r =>
      canonical_sum_prod (setspolynomial_normalize l)
        (setspolynomial_normalize r)
  | SetSPconst c => Cons_monom c Nil_var Nil_monom
  | SetSPvar i => Cons_varlist (Cons_var i Nil_var) Nil_monom
  end.

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

Definition setspolynomial_simplify (x:setspolynomial) :=
  canonical_sum_simplify (setspolynomial_normalize x).

Variable vm : varmap A.

Definition interp_var (i:index) := varmap_find Azero i vm.

Definition ivl_aux :=
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

Definition interp_m (c:A) (l:varlist) :=
  match l with
  | Nil_var => c
  | Cons_var x t => Amult c (ivl_aux x t)
  end.

Definition ics_aux :=
  (fix ics_aux (a:A) (s:canonical_sum) {struct s} : A :=
     match s with
     | Nil_monom => a
     | Cons_varlist l t => Aplus a (ics_aux (interp_vl l) t)
     | Cons_monom c l t => Aplus a (ics_aux (interp_m c l) t)
     end).

Definition interp_setcs (s:canonical_sum) : A :=
  match s with
  | Nil_monom => Azero
  | Cons_varlist l t => ics_aux (interp_vl l) t
  | Cons_monom c l t => ics_aux (interp_m c l) t
  end.

Fixpoint interp_setsp (p:setspolynomial) : A :=
  match p with
  | SetSPconst c => c
  | SetSPvar i => interp_var i
  | SetSPplus p1 p2 => Aplus (interp_setsp p1) (interp_setsp p2)
  | SetSPmult p1 p2 => Amult (interp_setsp p1) (interp_setsp p2)
  end.

(* End interpretation. *)

Unset Implicit Arguments.

(* Section properties. *)

Variable T : Semi_Setoid_Ring_Theory Aequiv Aplus Amult Aone Azero Aeq.

Hint Resolve (SSR_plus_comm T).
Hint Resolve (SSR_plus_assoc T).
Hint Resolve (SSR_plus_assoc2 S T).
Hint Resolve (SSR_mult_comm T).
Hint Resolve (SSR_mult_assoc T).
Hint Resolve (SSR_mult_assoc2 S T).
Hint Resolve (SSR_plus_zero_left T).
Hint Resolve (SSR_plus_zero_left2 S T).
Hint Resolve (SSR_mult_one_left T).
Hint Resolve (SSR_mult_one_left2 S T).
Hint Resolve (SSR_mult_zero_left T).
Hint Resolve (SSR_mult_zero_left2 S T).
Hint Resolve (SSR_distr_left T).
Hint Resolve (SSR_distr_left2 S T).
Hint Resolve (SSR_plus_reg_left T).
Hint Resolve (SSR_plus_permute S plus_morph T).
Hint Resolve (SSR_mult_permute S mult_morph T).
Hint Resolve (SSR_distr_right S plus_morph T).
Hint Resolve (SSR_distr_right2 S plus_morph T).
Hint Resolve (SSR_mult_zero_right S T).
Hint Resolve (SSR_mult_zero_right2 S T).
Hint Resolve (SSR_plus_zero_right S T).
Hint Resolve (SSR_plus_zero_right2 S T).
Hint Resolve (SSR_mult_one_right S T).
Hint Resolve (SSR_mult_one_right2 S T).
Hint Resolve (SSR_plus_reg_right S T).
Hint Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
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
   Aequiv (ivl_aux i v) (Amult (interp_var i) (interp_vl v)).
Proof.
  simple induction v; simpl in |- *; intros.
  trivial.
  rewrite (H i); trivial.
Qed.

Lemma varlist_merge_ok :
 forall x y:varlist,
   Aequiv (interp_vl (varlist_merge x y)) (Amult (interp_vl x) (interp_vl y)).
Proof.
  simple induction x.
  simpl in |- *; trivial.
  simple induction y.
  simpl in |- *; trivial.
  simpl in |- *; intros.
  elim (index_lt i i0); simpl in |- *; intros.

  rewrite (ivl_aux_ok v i).
  rewrite (ivl_aux_ok v0 i0).
  rewrite (ivl_aux_ok (varlist_merge v (Cons_var i0 v0)) i).
  rewrite (H (Cons_var i0 v0)).
  simpl in |- *.
  rewrite (ivl_aux_ok v0 i0).
  eauto.

  rewrite (ivl_aux_ok v i).
  rewrite (ivl_aux_ok v0 i0).
  rewrite
   (ivl_aux_ok
      ((fix vm_aux (l2:varlist) : varlist :=
          match l2 with
          | Nil_var => Cons_var i v
          | Cons_var v2 t2 =>
              if index_lt i v2
              then Cons_var i (varlist_merge v l2)
              else Cons_var v2 (vm_aux t2)
          end) v0) i0).
  rewrite H0.
  rewrite (ivl_aux_ok v i).
  eauto.
Qed.

Remark ics_aux_ok :
 forall (x:A) (s:canonical_sum),
   Aequiv (ics_aux x s) (Aplus x (interp_setcs s)).
Proof.
 simple induction s; simpl in |- *; intros; trivial.
Qed.

Remark interp_m_ok :
 forall (x:A) (l:varlist), Aequiv (interp_m x l) (Amult x (interp_vl l)).
Proof.
  destruct l as [| i v]; trivial.
Qed.

Hint Resolve ivl_aux_ok.
Hint Resolve ics_aux_ok.
Hint Resolve interp_m_ok.

(* Hints Resolve ivl_aux_ok ics_aux_ok interp_m_ok. *)

Lemma canonical_sum_merge_ok :
 forall x y:canonical_sum,
   Aequiv (interp_setcs (canonical_sum_merge x y))
     (Aplus (interp_setcs x) (interp_setcs y)).
Proof.
simple induction x; simpl in |- *.
trivial.

simple induction y; simpl in |- *; intros.
eauto.

generalize (varlist_eq_prop v v0).
elim (varlist_eq v v0).
intros; rewrite (H1 I).
simpl in |- *.
rewrite (ics_aux_ok (interp_m a v0) c).
rewrite (ics_aux_ok (interp_m a0 v0) c0).
rewrite (ics_aux_ok (interp_m (Aplus a a0) v0) (canonical_sum_merge c c0)).
rewrite (H c0).
rewrite (interp_m_ok (Aplus a a0) v0).
rewrite (interp_m_ok a v0).
rewrite (interp_m_ok a0 v0).
setoid_replace (Amult (Aplus a a0) (interp_vl v0)) with
 (Aplus (Amult a (interp_vl v0)) (Amult a0 (interp_vl v0)));
 [ idtac | trivial ].
setoid_replace
 (Aplus (Aplus (Amult a (interp_vl v0)) (Amult a0 (interp_vl v0)))
    (Aplus (interp_setcs c) (interp_setcs c0))) with
 (Aplus (Amult a (interp_vl v0))
    (Aplus (Amult a0 (interp_vl v0))
       (Aplus (interp_setcs c) (interp_setcs c0))));
 [ idtac | trivial ].
setoid_replace
 (Aplus (Aplus (Amult a (interp_vl v0)) (interp_setcs c))
    (Aplus (Amult a0 (interp_vl v0)) (interp_setcs c0))) with
 (Aplus (Amult a (interp_vl v0))
    (Aplus (interp_setcs c)
       (Aplus (Amult a0 (interp_vl v0)) (interp_setcs c0))));
 [ idtac | trivial ].
auto.

elim (varlist_lt v v0); simpl in |- *.
intro.
rewrite
 (ics_aux_ok (interp_m a v) (canonical_sum_merge c (Cons_monom a0 v0 c0)))
 .
rewrite (ics_aux_ok (interp_m a v) c).
rewrite (ics_aux_ok (interp_m a0 v0) c0).
rewrite (H (Cons_monom a0 v0 c0)); simpl in |- *.
rewrite (ics_aux_ok (interp_m a0 v0) c0); auto.

intro.
rewrite
 (ics_aux_ok (interp_m a0 v0)
    ((fix csm_aux (s2:canonical_sum) : canonical_sum :=
        match s2 with
        | Nil_monom => Cons_monom a v c
        | Cons_monom c2 l2 t2 =>
            if varlist_eq v l2
            then Cons_monom (Aplus a c2) v (canonical_sum_merge c t2)
            else
             if varlist_lt v l2
             then Cons_monom a v (canonical_sum_merge c s2)
             else Cons_monom c2 l2 (csm_aux t2)
        | Cons_varlist l2 t2 =>
            if varlist_eq v l2
            then Cons_monom (Aplus a Aone) v (canonical_sum_merge c t2)
            else
             if varlist_lt v l2
             then Cons_monom a v (canonical_sum_merge c s2)
             else Cons_varlist l2 (csm_aux t2)
        end) c0)).
rewrite H0.
rewrite (ics_aux_ok (interp_m a v) c);
 rewrite (ics_aux_ok (interp_m a0 v0) c0); simpl in |- *;
 auto.

generalize (varlist_eq_prop v v0).
elim (varlist_eq v v0).
intros; rewrite (H1 I).
simpl in |- *.
rewrite (ics_aux_ok (interp_m (Aplus a Aone) v0) (canonical_sum_merge c c0));
 rewrite (ics_aux_ok (interp_m a v0) c);
 rewrite (ics_aux_ok (interp_vl v0) c0).
rewrite (H c0).
rewrite (interp_m_ok (Aplus a Aone) v0).
rewrite (interp_m_ok a v0).
setoid_replace (Amult (Aplus a Aone) (interp_vl v0)) with
 (Aplus (Amult a (interp_vl v0)) (Amult Aone (interp_vl v0)));
 [ idtac | trivial ].
setoid_replace
 (Aplus (Aplus (Amult a (interp_vl v0)) (Amult Aone (interp_vl v0)))
    (Aplus (interp_setcs c) (interp_setcs c0))) with
 (Aplus (Amult a (interp_vl v0))
    (Aplus (Amult Aone (interp_vl v0))
       (Aplus (interp_setcs c) (interp_setcs c0))));
 [ idtac | trivial ].
setoid_replace
 (Aplus (Aplus (Amult a (interp_vl v0)) (interp_setcs c))
    (Aplus (interp_vl v0) (interp_setcs c0))) with
 (Aplus (Amult a (interp_vl v0))
    (Aplus (interp_setcs c) (Aplus (interp_vl v0) (interp_setcs c0))));
 [ idtac | trivial ].
setoid_replace (Amult Aone (interp_vl v0)) with (interp_vl v0);
 [ idtac | trivial ].
auto.

elim (varlist_lt v v0); simpl in |- *.
intro.
rewrite
 (ics_aux_ok (interp_m a v) (canonical_sum_merge c (Cons_varlist v0 c0)))
 ; rewrite (ics_aux_ok (interp_m a v) c);
 rewrite (ics_aux_ok (interp_vl v0) c0).
rewrite (H (Cons_varlist v0 c0)); simpl in |- *.
rewrite (ics_aux_ok (interp_vl v0) c0).
auto.

intro.
rewrite
 (ics_aux_ok (interp_vl v0)
    ((fix csm_aux (s2:canonical_sum) : canonical_sum :=
        match s2 with
        | Nil_monom => Cons_monom a v c
        | Cons_monom c2 l2 t2 =>
            if varlist_eq v l2
            then Cons_monom (Aplus a c2) v (canonical_sum_merge c t2)
            else
             if varlist_lt v l2
             then Cons_monom a v (canonical_sum_merge c s2)
             else Cons_monom c2 l2 (csm_aux t2)
        | Cons_varlist l2 t2 =>
            if varlist_eq v l2
            then Cons_monom (Aplus a Aone) v (canonical_sum_merge c t2)
            else
             if varlist_lt v l2
             then Cons_monom a v (canonical_sum_merge c s2)
             else Cons_varlist l2 (csm_aux t2)
        end) c0)); rewrite H0.
rewrite (ics_aux_ok (interp_m a v) c); rewrite (ics_aux_ok (interp_vl v0) c0);
 simpl in |- *.
auto.

simple induction y; simpl in |- *; intros.
trivial.

generalize (varlist_eq_prop v v0).
elim (varlist_eq v v0).
intros; rewrite (H1 I).
simpl in |- *.
rewrite (ics_aux_ok (interp_m (Aplus Aone a) v0) (canonical_sum_merge c c0));
 rewrite (ics_aux_ok (interp_vl v0) c);
 rewrite (ics_aux_ok (interp_m a v0) c0); rewrite (H c0).
rewrite (interp_m_ok (Aplus Aone a) v0); rewrite (interp_m_ok a v0).
setoid_replace (Amult (Aplus Aone a) (interp_vl v0)) with
 (Aplus (Amult Aone (interp_vl v0)) (Amult a (interp_vl v0)));
 [ idtac | trivial ].
setoid_replace
 (Aplus (Aplus (Amult Aone (interp_vl v0)) (Amult a (interp_vl v0)))
    (Aplus (interp_setcs c) (interp_setcs c0))) with
 (Aplus (Amult Aone (interp_vl v0))
    (Aplus (Amult a (interp_vl v0))
       (Aplus (interp_setcs c) (interp_setcs c0))));
 [ idtac | trivial ].
setoid_replace
 (Aplus (Aplus (interp_vl v0) (interp_setcs c))
    (Aplus (Amult a (interp_vl v0)) (interp_setcs c0))) with
 (Aplus (interp_vl v0)
    (Aplus (interp_setcs c)
       (Aplus (Amult a (interp_vl v0)) (interp_setcs c0))));
 [ idtac | trivial ].
auto.

elim (varlist_lt v v0); simpl in |- *; intros.
rewrite
 (ics_aux_ok (interp_vl v) (canonical_sum_merge c (Cons_monom a v0 c0)))
 ; rewrite (ics_aux_ok (interp_vl v) c);
 rewrite (ics_aux_ok (interp_m a v0) c0).
rewrite (H (Cons_monom a v0 c0)); simpl in |- *.
rewrite (ics_aux_ok (interp_m a v0) c0); auto.

rewrite
 (ics_aux_ok (interp_m a v0)
    ((fix csm_aux2 (s2:canonical_sum) : canonical_sum :=
        match s2 with
        | Nil_monom => Cons_varlist v c
        | Cons_monom c2 l2 t2 =>
            if varlist_eq v l2
            then Cons_monom (Aplus Aone c2) v (canonical_sum_merge c t2)
            else
             if varlist_lt v l2
             then Cons_varlist v (canonical_sum_merge c s2)
             else Cons_monom c2 l2 (csm_aux2 t2)
        | Cons_varlist l2 t2 =>
            if varlist_eq v l2
            then Cons_monom (Aplus Aone Aone) v (canonical_sum_merge c t2)
            else
             if varlist_lt v l2
             then Cons_varlist v (canonical_sum_merge c s2)
             else Cons_varlist l2 (csm_aux2 t2)
        end) c0)); rewrite H0.
rewrite (ics_aux_ok (interp_vl v) c); rewrite (ics_aux_ok (interp_m a v0) c0);
 simpl in |- *; auto.

generalize (varlist_eq_prop v v0).
elim (varlist_eq v v0); intros.
rewrite (H1 I); simpl in |- *.
rewrite
 (ics_aux_ok (interp_m (Aplus Aone Aone) v0) (canonical_sum_merge c c0))
 ; rewrite (ics_aux_ok (interp_vl v0) c);
 rewrite (ics_aux_ok (interp_vl v0) c0); rewrite (H c0).
rewrite (interp_m_ok (Aplus Aone Aone) v0).
setoid_replace (Amult (Aplus Aone Aone) (interp_vl v0)) with
 (Aplus (Amult Aone (interp_vl v0)) (Amult Aone (interp_vl v0)));
 [ idtac | trivial ].
setoid_replace
 (Aplus (Aplus (Amult Aone (interp_vl v0)) (Amult Aone (interp_vl v0)))
    (Aplus (interp_setcs c) (interp_setcs c0))) with
 (Aplus (Amult Aone (interp_vl v0))
    (Aplus (Amult Aone (interp_vl v0))
       (Aplus (interp_setcs c) (interp_setcs c0))));
 [ idtac | trivial ].
setoid_replace
 (Aplus (Aplus (interp_vl v0) (interp_setcs c))
    (Aplus (interp_vl v0) (interp_setcs c0))) with
 (Aplus (interp_vl v0)
    (Aplus (interp_setcs c) (Aplus (interp_vl v0) (interp_setcs c0))));
[ idtac | trivial ].
setoid_replace (Amult Aone (interp_vl v0)) with (interp_vl v0); auto.

elim (varlist_lt v v0); simpl in |- *.
rewrite
 (ics_aux_ok (interp_vl v) (canonical_sum_merge c (Cons_varlist v0 c0)))
 ; rewrite (ics_aux_ok (interp_vl v) c);
 rewrite (ics_aux_ok (interp_vl v0) c0); rewrite (H (Cons_varlist v0 c0));
 simpl in |- *.
rewrite (ics_aux_ok (interp_vl v0) c0); auto.

rewrite
 (ics_aux_ok (interp_vl v0)
    ((fix csm_aux2 (s2:canonical_sum) : canonical_sum :=
        match s2 with
        | Nil_monom => Cons_varlist v c
        | Cons_monom c2 l2 t2 =>
            if varlist_eq v l2
            then Cons_monom (Aplus Aone c2) v (canonical_sum_merge c t2)
            else
             if varlist_lt v l2
             then Cons_varlist v (canonical_sum_merge c s2)
             else Cons_monom c2 l2 (csm_aux2 t2)
        | Cons_varlist l2 t2 =>
            if varlist_eq v l2
            then Cons_monom (Aplus Aone Aone) v (canonical_sum_merge c t2)
            else
             if varlist_lt v l2
             then Cons_varlist v (canonical_sum_merge c s2)
             else Cons_varlist l2 (csm_aux2 t2)
        end) c0)); rewrite H0.
rewrite (ics_aux_ok (interp_vl v) c); rewrite (ics_aux_ok (interp_vl v0) c0);
 simpl in |- *; auto.
Qed.

Lemma monom_insert_ok :
 forall (a:A) (l:varlist) (s:canonical_sum),
   Aequiv (interp_setcs (monom_insert a l s))
     (Aplus (Amult a (interp_vl l)) (interp_setcs s)).
Proof.
simple induction s; intros.
simpl in |- *; rewrite (interp_m_ok a l); trivial.

simpl in |- *; generalize (varlist_eq_prop l v); elim (varlist_eq l v).
intro Hr; rewrite (Hr I); simpl in |- *.
rewrite (ics_aux_ok (interp_m (Aplus a a0) v) c);
 rewrite (ics_aux_ok (interp_m a0 v) c).
rewrite (interp_m_ok (Aplus a a0) v); rewrite (interp_m_ok a0 v).
setoid_replace (Amult (Aplus a a0) (interp_vl v)) with
 (Aplus (Amult a (interp_vl v)) (Amult a0 (interp_vl v)));
 [ idtac | trivial ].
auto.

elim (varlist_lt l v); simpl in |- *; intros.
rewrite (ics_aux_ok (interp_m a0 v) c).
rewrite (interp_m_ok a0 v); rewrite (interp_m_ok a l).
auto.

rewrite (ics_aux_ok (interp_m a0 v) (monom_insert a l c));
 rewrite (ics_aux_ok (interp_m a0 v) c); rewrite H.
auto.

simpl in |- *.
generalize (varlist_eq_prop l v); elim (varlist_eq l v).
intro Hr; rewrite (Hr I); simpl in |- *.
rewrite (ics_aux_ok (interp_m (Aplus a Aone) v) c);
 rewrite (ics_aux_ok (interp_vl v) c).
rewrite (interp_m_ok (Aplus a Aone) v).
setoid_replace (Amult (Aplus a Aone) (interp_vl v)) with
 (Aplus (Amult a (interp_vl v)) (Amult Aone (interp_vl v)));
 [ idtac | trivial ].
setoid_replace (Amult Aone (interp_vl v)) with (interp_vl v);
 [ idtac | trivial ].
auto.

elim (varlist_lt l v); simpl in |- *; intros; auto.
rewrite (ics_aux_ok (interp_vl v) (monom_insert a l c)); rewrite H.
rewrite (ics_aux_ok (interp_vl v) c); auto.
Qed.

Lemma varlist_insert_ok :
 forall (l:varlist) (s:canonical_sum),
   Aequiv (interp_setcs (varlist_insert l s))
     (Aplus (interp_vl l) (interp_setcs s)).
Proof.
simple induction s; simpl in |- *; intros.
trivial.

generalize (varlist_eq_prop l v); elim (varlist_eq l v).
intro Hr; rewrite (Hr I); simpl in |- *.
rewrite (ics_aux_ok (interp_m (Aplus Aone a) v) c);
 rewrite (ics_aux_ok (interp_m a v) c).
rewrite (interp_m_ok (Aplus Aone a) v); rewrite (interp_m_ok a v).
setoid_replace (Amult (Aplus Aone a) (interp_vl v)) with
 (Aplus (Amult Aone (interp_vl v)) (Amult a (interp_vl v)));
 [ idtac | trivial ].
setoid_replace (Amult Aone (interp_vl v)) with (interp_vl v); auto.

elim (varlist_lt l v); simpl in |- *; intros; auto.
rewrite (ics_aux_ok (interp_m a v) (varlist_insert l c));
 rewrite (ics_aux_ok (interp_m a v) c).
rewrite (interp_m_ok a v).
rewrite H; auto.

generalize (varlist_eq_prop l v); elim (varlist_eq l v).
intro Hr; rewrite (Hr I); simpl in |- *.
rewrite (ics_aux_ok (interp_m (Aplus Aone Aone) v) c);
 rewrite (ics_aux_ok (interp_vl v) c).
rewrite (interp_m_ok (Aplus Aone Aone) v).
setoid_replace (Amult (Aplus Aone Aone) (interp_vl v)) with
 (Aplus (Amult Aone (interp_vl v)) (Amult Aone (interp_vl v)));
 [ idtac | trivial ].
setoid_replace (Amult Aone (interp_vl v)) with (interp_vl v); auto.

elim (varlist_lt l v); simpl in |- *; intros; auto.
rewrite (ics_aux_ok (interp_vl v) (varlist_insert l c)).
rewrite H.
rewrite (ics_aux_ok (interp_vl v) c); auto.
Qed.

Lemma canonical_sum_scalar_ok :
 forall (a:A) (s:canonical_sum),
   Aequiv (interp_setcs (canonical_sum_scalar a s))
     (Amult a (interp_setcs s)).
Proof.
simple induction s; simpl in |- *; intros.
trivial.

rewrite (ics_aux_ok (interp_m (Amult a a0) v) (canonical_sum_scalar a c));
 rewrite (ics_aux_ok (interp_m a0 v) c).
rewrite (interp_m_ok (Amult a a0) v); rewrite (interp_m_ok a0 v).
rewrite H.
setoid_replace (Amult a (Aplus (Amult a0 (interp_vl v)) (interp_setcs c)))
 with (Aplus (Amult a (Amult a0 (interp_vl v))) (Amult a (interp_setcs c)));
 [ idtac | trivial ].
auto.

rewrite (ics_aux_ok (interp_m a v) (canonical_sum_scalar a c));
 rewrite (ics_aux_ok (interp_vl v) c); rewrite H.
rewrite (interp_m_ok a v).
auto.
Qed.

Lemma canonical_sum_scalar2_ok :
 forall (l:varlist) (s:canonical_sum),
   Aequiv (interp_setcs (canonical_sum_scalar2 l s))
     (Amult (interp_vl l) (interp_setcs s)).
Proof.
simple induction s; simpl in |- *; intros; auto.
rewrite (monom_insert_ok a (varlist_merge l v) (canonical_sum_scalar2 l c)).
rewrite (ics_aux_ok (interp_m a v) c).
rewrite (interp_m_ok a v).
rewrite H.
rewrite (varlist_merge_ok l v).
setoid_replace
 (Amult (interp_vl l) (Aplus (Amult a (interp_vl v)) (interp_setcs c))) with
 (Aplus (Amult (interp_vl l) (Amult a (interp_vl v)))
    (Amult (interp_vl l) (interp_setcs c)));
 [ idtac | trivial ].
auto.

rewrite (varlist_insert_ok (varlist_merge l v) (canonical_sum_scalar2 l c)).
rewrite (ics_aux_ok (interp_vl v) c).
rewrite H.
rewrite (varlist_merge_ok l v).
auto.
Qed.

Lemma canonical_sum_scalar3_ok :
 forall (c:A) (l:varlist) (s:canonical_sum),
   Aequiv (interp_setcs (canonical_sum_scalar3 c l s))
     (Amult c (Amult (interp_vl l) (interp_setcs s))).
Proof.
simple induction s; simpl in |- *; intros.
rewrite (SSR_mult_zero_right S T (interp_vl l)).
auto.

rewrite
 (monom_insert_ok (Amult c a) (varlist_merge l v)
    (canonical_sum_scalar3 c l c0)).
rewrite (ics_aux_ok (interp_m a v) c0).
rewrite (interp_m_ok a v).
rewrite H.
rewrite (varlist_merge_ok l v).
setoid_replace
 (Amult (interp_vl l) (Aplus (Amult a (interp_vl v)) (interp_setcs c0))) with
 (Aplus (Amult (interp_vl l) (Amult a (interp_vl v)))
    (Amult (interp_vl l) (interp_setcs c0)));
 [ idtac | trivial ].
setoid_replace
 (Amult c
    (Aplus (Amult (interp_vl l) (Amult a (interp_vl v)))
       (Amult (interp_vl l) (interp_setcs c0)))) with
 (Aplus (Amult c (Amult (interp_vl l) (Amult a (interp_vl v))))
    (Amult c (Amult (interp_vl l) (interp_setcs c0))));
 [ idtac | trivial ].
setoid_replace (Amult (Amult c a) (Amult (interp_vl l) (interp_vl v))) with
 (Amult c (Amult a (Amult (interp_vl l) (interp_vl v))));
 [ idtac | trivial ].
auto.

rewrite
 (monom_insert_ok c (varlist_merge l v) (canonical_sum_scalar3 c l c0))
 .
rewrite (ics_aux_ok (interp_vl v) c0).
rewrite H.
rewrite (varlist_merge_ok l v).
setoid_replace
 (Aplus (Amult c (Amult (interp_vl l) (interp_vl v)))
    (Amult c (Amult (interp_vl l) (interp_setcs c0)))) with
 (Amult c
    (Aplus (Amult (interp_vl l) (interp_vl v))
       (Amult (interp_vl l) (interp_setcs c0))));
 [ idtac | trivial ].
auto.
Qed.

Lemma canonical_sum_prod_ok :
 forall x y:canonical_sum,
   Aequiv (interp_setcs (canonical_sum_prod x y))
     (Amult (interp_setcs x) (interp_setcs y)).
Proof.
simple induction x; simpl in |- *; intros.
trivial.

rewrite
 (canonical_sum_merge_ok (canonical_sum_scalar3 a v y)
    (canonical_sum_prod c y)).
rewrite (canonical_sum_scalar3_ok a v y).
rewrite (ics_aux_ok (interp_m a v) c).
rewrite (interp_m_ok a v).
rewrite (H y).
setoid_replace (Amult a (Amult (interp_vl v) (interp_setcs y))) with
 (Amult (Amult a (interp_vl v)) (interp_setcs y));
 [ idtac | trivial ].
setoid_replace
 (Amult (Aplus (Amult a (interp_vl v)) (interp_setcs c)) (interp_setcs y))
 with
 (Aplus (Amult (Amult a (interp_vl v)) (interp_setcs y))
    (Amult (interp_setcs c) (interp_setcs y)));
 [ idtac | trivial ].
trivial.

rewrite
 (canonical_sum_merge_ok (canonical_sum_scalar2 v y) (canonical_sum_prod c y))
 .
rewrite (canonical_sum_scalar2_ok v y).
rewrite (ics_aux_ok (interp_vl v) c).
rewrite (H y).
trivial.
Qed.

Theorem setspolynomial_normalize_ok :
 forall p:setspolynomial,
   Aequiv (interp_setcs (setspolynomial_normalize p)) (interp_setsp p).
Proof.
simple induction p; simpl in |- *; intros; trivial.
rewrite
 (canonical_sum_merge_ok (setspolynomial_normalize s)
    (setspolynomial_normalize s0)).
rewrite H; rewrite H0; trivial.

rewrite
 (canonical_sum_prod_ok (setspolynomial_normalize s)
    (setspolynomial_normalize s0)).
rewrite H; rewrite H0; trivial.
Qed.

Lemma canonical_sum_simplify_ok :
 forall s:canonical_sum,
   Aequiv (interp_setcs (canonical_sum_simplify s)) (interp_setcs s).
Proof.
simple induction s; simpl in |- *; intros.
trivial.

generalize (SSR_eq_prop T a Azero).
elim (Aeq a Azero).
simpl in |- *.
intros.
rewrite (ics_aux_ok (interp_m a v) c).
rewrite (interp_m_ok a v).
rewrite (H0 I).
setoid_replace (Amult Azero (interp_vl v)) with Azero;
 [ idtac | trivial ].
rewrite H.
trivial.

intros; simpl in |- *.
generalize (SSR_eq_prop T a Aone).
elim (Aeq a Aone).
intros.
rewrite (ics_aux_ok (interp_m a v) c).
rewrite (interp_m_ok a v).
rewrite (H1 I).
simpl in |- *.
rewrite (ics_aux_ok (interp_vl v) (canonical_sum_simplify c)).
rewrite H.
auto.

simpl in |- *.
intros.
rewrite (ics_aux_ok (interp_m a v) (canonical_sum_simplify c)).
rewrite (ics_aux_ok (interp_m a v) c).
rewrite H; trivial.

rewrite (ics_aux_ok (interp_vl v) (canonical_sum_simplify c)).
rewrite H.
auto.
Qed.

Theorem setspolynomial_simplify_ok :
 forall p:setspolynomial,
   Aequiv (interp_setcs (setspolynomial_simplify p)) (interp_setsp p).
Proof.
intro.
unfold setspolynomial_simplify in |- *.
rewrite (canonical_sum_simplify_ok (setspolynomial_normalize p)).
exact (setspolynomial_normalize_ok p).
Qed.

End semi_setoid_rings.

Implicit Arguments Cons_varlist.
Implicit Arguments Cons_monom.
Implicit Arguments SetSPconst.
Implicit Arguments SetSPplus.
Implicit Arguments SetSPmult.



Section setoid_rings.

Set Implicit Arguments.

Variable vm : varmap A.
Variable T : Setoid_Ring_Theory Aequiv Aplus Amult Aone Azero Aopp Aeq.

Hint Resolve (STh_plus_comm T).
Hint Resolve (STh_plus_assoc T).
Hint Resolve (STh_plus_assoc2 S T).
Hint Resolve (STh_mult_comm T).
Hint Resolve (STh_mult_assoc T).
Hint Resolve (STh_mult_assoc2 S T).
Hint Resolve (STh_plus_zero_left T).
Hint Resolve (STh_plus_zero_left2 S T).
Hint Resolve (STh_mult_one_left T).
Hint Resolve (STh_mult_one_left2 S T).
Hint Resolve (STh_mult_zero_left S plus_morph mult_morph T).
Hint Resolve (STh_mult_zero_left2 S plus_morph mult_morph T).
Hint Resolve (STh_distr_left T).
Hint Resolve (STh_distr_left2 S T).
Hint Resolve (STh_plus_reg_left S plus_morph T).
Hint Resolve (STh_plus_permute S plus_morph T).
Hint Resolve (STh_mult_permute S mult_morph T).
Hint Resolve (STh_distr_right S plus_morph T).
Hint Resolve (STh_distr_right2 S plus_morph T).
Hint Resolve (STh_mult_zero_right S plus_morph mult_morph T).
Hint Resolve (STh_mult_zero_right2 S plus_morph mult_morph T).
Hint Resolve (STh_plus_zero_right S T).
Hint Resolve (STh_plus_zero_right2 S T).
Hint Resolve (STh_mult_one_right S T).
Hint Resolve (STh_mult_one_right2 S T).
Hint Resolve (STh_plus_reg_right S plus_morph T).
Hint Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
Hint Immediate T.


(*** Definitions *)

Inductive setpolynomial : Type :=
  | SetPvar : index -> setpolynomial
  | SetPconst : A -> setpolynomial
  | SetPplus : setpolynomial -> setpolynomial -> setpolynomial
  | SetPmult : setpolynomial -> setpolynomial -> setpolynomial
  | SetPopp : setpolynomial -> setpolynomial.

Fixpoint setpolynomial_normalize (x:setpolynomial) : canonical_sum :=
  match x with
  | SetPplus l r =>
      canonical_sum_merge (setpolynomial_normalize l)
        (setpolynomial_normalize r)
  | SetPmult l r =>
      canonical_sum_prod (setpolynomial_normalize l)
        (setpolynomial_normalize r)
  | SetPconst c => Cons_monom c Nil_var Nil_monom
  | SetPvar i => Cons_varlist (Cons_var i Nil_var) Nil_monom
  | SetPopp p =>
      canonical_sum_scalar3 (Aopp Aone) Nil_var (setpolynomial_normalize p)
  end.

Definition setpolynomial_simplify (x:setpolynomial) :=
  canonical_sum_simplify (setpolynomial_normalize x).

Fixpoint setspolynomial_of (x:setpolynomial) : setspolynomial :=
  match x with
  | SetPplus l r => SetSPplus (setspolynomial_of l) (setspolynomial_of r)
  | SetPmult l r => SetSPmult (setspolynomial_of l) (setspolynomial_of r)
  | SetPconst c => SetSPconst c
  | SetPvar i => SetSPvar i
  | SetPopp p => SetSPmult (SetSPconst (Aopp Aone)) (setspolynomial_of p)
  end.

(*** Interpretation *)

Fixpoint interp_setp (p:setpolynomial) : A :=
  match p with
  | SetPconst c => c
  | SetPvar i => varmap_find Azero i vm
  | SetPplus p1 p2 => Aplus (interp_setp p1) (interp_setp p2)
  | SetPmult p1 p2 => Amult (interp_setp p1) (interp_setp p2)
  | SetPopp p1 => Aopp (interp_setp p1)
  end.

(*** Properties *)

Unset Implicit Arguments.

Lemma setspolynomial_of_ok :
 forall p:setpolynomial,
   Aequiv (interp_setp p) (interp_setsp vm (setspolynomial_of p)).
simple induction p; trivial; simpl in |- *; intros.
rewrite H; rewrite H0; trivial.
rewrite H; rewrite H0; trivial.
rewrite H.
rewrite
 (STh_opp_mult_left2 S plus_morph mult_morph T Aone
    (interp_setsp vm (setspolynomial_of s))).
rewrite (STh_mult_one_left T (interp_setsp vm (setspolynomial_of s))).
trivial.
Qed.

Theorem setpolynomial_normalize_ok :
 forall p:setpolynomial,
   setpolynomial_normalize p = setspolynomial_normalize (setspolynomial_of p).
simple induction p; trivial; simpl in |- *; intros.
rewrite H; rewrite H0; reflexivity.
rewrite H; rewrite H0; reflexivity.
rewrite H; simpl in |- *.
elim
 (canonical_sum_scalar3 (Aopp Aone) Nil_var
    (setspolynomial_normalize (setspolynomial_of s)));
 [ reflexivity
 | simpl in |- *; intros; rewrite H0; reflexivity
 | simpl in |- *; intros; rewrite H0; reflexivity ].
Qed.

Theorem setpolynomial_simplify_ok :
 forall p:setpolynomial,
   Aequiv (interp_setcs vm (setpolynomial_simplify p)) (interp_setp p).
intro.
unfold setpolynomial_simplify in |- *.
rewrite (setspolynomial_of_ok p).
rewrite setpolynomial_normalize_ok.
rewrite
 (canonical_sum_simplify_ok vm
    (Semi_Setoid_Ring_Theory_of A Aequiv S Aplus Amult Aone Azero Aopp Aeq
       plus_morph mult_morph T)
    (setspolynomial_normalize (setspolynomial_of p)))
 .
rewrite
 (setspolynomial_normalize_ok vm
    (Semi_Setoid_Ring_Theory_of A Aequiv S Aplus Amult Aone Azero Aopp Aeq
       plus_morph mult_morph T) (setspolynomial_of p))
 .
trivial.
Qed.

End setoid_rings.

End setoid.
