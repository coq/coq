(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Ring_theory.
Require Quote.
Require Ring_normalize.

Section abstract_semi_rings.

Inductive Type aspolynomial :=
  ASPvar : index -> aspolynomial
| ASP0 : aspolynomial
| ASP1 : aspolynomial
| ASPplus : aspolynomial -> aspolynomial -> aspolynomial
| ASPmult : aspolynomial -> aspolynomial -> aspolynomial
.

Inductive abstract_sum : Type := 
| Nil_acs : abstract_sum
| Cons_acs : varlist -> abstract_sum -> abstract_sum
.

Fixpoint abstract_sum_merge [s1:abstract_sum] 
      	 : abstract_sum -> abstract_sum :=
Cases s1 of
| (Cons_acs l1 t1) =>      
     Fix asm_aux{asm_aux[s2:abstract_sum] : abstract_sum :=
           Cases s2 of
      	   | (Cons_acs l2 t2) =>
	       if (varlist_lt l1 l2)
	       then (Cons_acs l1 (abstract_sum_merge t1 s2))
	       else (Cons_acs l2 (asm_aux t2))
	   | Nil_acs => s1
	   end}
| Nil_acs => [s2]s2
end.

Fixpoint abstract_varlist_insert [l1:varlist; s2:abstract_sum] 
      : abstract_sum :=
  Cases s2 of
  | (Cons_acs l2 t2) =>
       if (varlist_lt l1 l2)
       then (Cons_acs l1 s2)
       else (Cons_acs l2 (abstract_varlist_insert l1 t2))
  | Nil_acs => (Cons_acs l1 Nil_acs)
  end.

Fixpoint abstract_sum_scalar [l1:varlist; s2:abstract_sum] 
      : abstract_sum :=
  Cases s2 of
  | (Cons_acs l2 t2) => (abstract_varlist_insert (varlist_merge l1 l2) 
                                (abstract_sum_scalar l1 t2))
  | Nil_acs => Nil_acs
  end.

Fixpoint abstract_sum_prod [s1:abstract_sum] 
      	 : abstract_sum -> abstract_sum := 
    [s2]Cases s1 of
    | (Cons_acs l1 t1) =>
	(abstract_sum_merge (abstract_sum_scalar l1 s2) 
			     (abstract_sum_prod t1 s2))
    | Nil_acs => Nil_acs
    end.

Fixpoint aspolynomial_normalize[p:aspolynomial] : abstract_sum :=
  Cases p of
  | (ASPvar i) => (Cons_acs (Cons_var i Nil_var) Nil_acs)
  | ASP1 => (Cons_acs Nil_var Nil_acs)
  | ASP0 => Nil_acs
  | (ASPplus l r) => (abstract_sum_merge (aspolynomial_normalize l) 
      	       	       	       	       	 (aspolynomial_normalize r))
  | (ASPmult l r) => (abstract_sum_prod (aspolynomial_normalize l) 
      	       	       	       	        (aspolynomial_normalize r))
  end.



Variable A : Type.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aeq : A -> A -> bool.
Variable vm : (varmap A).
Variable T : (Semi_Ring_Theory Aplus Amult Aone Azero Aeq).

Fixpoint interp_asp [p:aspolynomial] : A :=
  Cases p of
  | (ASPvar i) => (interp_var Azero vm i)
  | ASP0 => Azero
  | ASP1 => Aone
  | (ASPplus l r) => (Aplus (interp_asp l) (interp_asp r))
  | (ASPmult l r) => (Amult (interp_asp l) (interp_asp r))
  end.

(* Local *) Definition iacs_aux := Fix iacs_aux{iacs_aux [a:A; s:abstract_sum] : A :=  
  Cases s of
  | Nil_acs => a
  | (Cons_acs l t) => (Aplus a (iacs_aux (interp_vl Amult Aone Azero vm l) t))
  end}.

Definition interp_acs [s:abstract_sum] : A :=
  Cases s of
  | (Cons_acs l t) => (iacs_aux (interp_vl Amult Aone Azero vm l) t)
  | Nil_acs => Azero
  end.

Hint SR_plus_sym_T := Resolve (SR_plus_sym T).
Hint SR_plus_assoc_T := Resolve (SR_plus_assoc T).
Hint SR_plus_assoc2_T := Resolve (SR_plus_assoc2 T).
Hint SR_mult_sym_T := Resolve (SR_mult_sym T).
Hint SR_mult_assoc_T := Resolve (SR_mult_assoc T).
Hint SR_mult_assoc2_T := Resolve (SR_mult_assoc2 T).
Hint SR_plus_zero_left_T := Resolve (SR_plus_zero_left T).
Hint SR_plus_zero_left2_T := Resolve (SR_plus_zero_left2 T).
Hint SR_mult_one_left_T := Resolve (SR_mult_one_left T).
Hint SR_mult_one_left2_T := Resolve (SR_mult_one_left2 T).
Hint SR_mult_zero_left_T := Resolve (SR_mult_zero_left T).
Hint SR_mult_zero_left2_T := Resolve (SR_mult_zero_left2 T).
Hint SR_distr_left_T := Resolve (SR_distr_left T).
Hint SR_distr_left2_T := Resolve (SR_distr_left2 T).
Hint SR_plus_reg_left_T := Resolve (SR_plus_reg_left T).
Hint SR_plus_permute_T := Resolve (SR_plus_permute T).
Hint SR_mult_permute_T := Resolve (SR_mult_permute T).
Hint SR_distr_right_T := Resolve (SR_distr_right T).
Hint SR_distr_right2_T := Resolve (SR_distr_right2 T).
Hint SR_mult_zero_right_T := Resolve (SR_mult_zero_right T).
Hint SR_mult_zero_right2_T := Resolve (SR_mult_zero_right2 T).
Hint SR_plus_zero_right_T := Resolve (SR_plus_zero_right T).
Hint SR_plus_zero_right2_T := Resolve (SR_plus_zero_right2 T).
Hint SR_mult_one_right_T := Resolve (SR_mult_one_right T).
Hint SR_mult_one_right2_T := Resolve (SR_mult_one_right2 T).
Hint SR_plus_reg_right_T := Resolve (SR_plus_reg_right T).
Hints Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
Hints Immediate T.

Remark iacs_aux_ok : (x:A)(s:abstract_sum)
  (iacs_aux x s)==(Aplus x (interp_acs s)).
Proof.
  Induction s; Simpl; Intros.
  Trivial.
  Reflexivity.
Save.

Hint rew_iacs_aux : core := Extern 10 (eqT A ? ?) Rewrite iacs_aux_ok.

Lemma abstract_varlist_insert_ok : (l:varlist)(s:abstract_sum)
  (interp_acs (abstract_varlist_insert l s)) 
   ==(Aplus (interp_vl Amult Aone Azero vm l) (interp_acs s)).

  Induction s.
  Trivial.

  Simpl; Intros.
  Elim (varlist_lt l v); Simpl.  	
  EAuto.
  Rewrite iacs_aux_ok.
  Rewrite H; Auto.

Save.

Lemma abstract_sum_merge_ok : (x,y:abstract_sum)
  (interp_acs (abstract_sum_merge x y))
  ==(Aplus (interp_acs x) (interp_acs y)).

Proof.  
  Induction x.
  Trivial.
  Induction y; Intros.

  Auto.

  Simpl; Elim (varlist_lt v v0); Simpl.
  Repeat Rewrite iacs_aux_ok.
  Rewrite H;  Simpl; Auto.

  Simpl in H0.
  Repeat Rewrite iacs_aux_ok.
  Rewrite H0. Simpl; Auto.
Save.

Lemma abstract_sum_scalar_ok : (l:varlist)(s:abstract_sum)
  (interp_acs (abstract_sum_scalar l s)) 
   == (Amult (interp_vl Amult Aone Azero vm l) (interp_acs s)).
Proof.
  Induction s.
  Simpl; EAuto.

  Simpl; Intros.
  Rewrite iacs_aux_ok.
  Rewrite abstract_varlist_insert_ok.
  Rewrite H.
  Rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  Auto.
Save.

Lemma abstract_sum_prod_ok : (x,y:abstract_sum)
  (interp_acs (abstract_sum_prod x y)) 
   == (Amult (interp_acs x) (interp_acs y)).

Proof.
  Induction x.
  Intros; Simpl; EAuto.

  NewDestruct y; Intros.

  Simpl; Rewrite H; EAuto.

  Unfold abstract_sum_prod; Fold abstract_sum_prod.
  Rewrite abstract_sum_merge_ok.
  Rewrite abstract_sum_scalar_ok.
  Rewrite H; Simpl; Auto.
Save.

Theorem aspolynomial_normalize_ok : (x:aspolynomial)
	(interp_asp x)==(interp_acs (aspolynomial_normalize x)).
Proof.
  Induction x; Simpl; Intros; Trivial.
  Rewrite abstract_sum_merge_ok.
  Rewrite H; Rewrite H0; EAuto.
  Rewrite abstract_sum_prod_ok.
  Rewrite H; Rewrite H0; EAuto.
Save.

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

Inductive Type apolynomial :=
  APvar : index -> apolynomial
| AP0 : apolynomial
| AP1 : apolynomial
| APplus : apolynomial -> apolynomial -> apolynomial
| APmult : apolynomial -> apolynomial -> apolynomial
| APopp : apolynomial -> apolynomial
.

(* A canonical "abstract" sum is a list of varlist with the sign "+" or "-".
   Invariant : the list is sorted and there is no varlist is present
   with both signs. +x +x +x -x is forbidden => the canonical form is +x+x *)

Inductive signed_sum : Type := 
| Nil_varlist : signed_sum
| Plus_varlist : varlist -> signed_sum -> signed_sum
| Minus_varlist : varlist -> signed_sum -> signed_sum
.

Fixpoint signed_sum_merge [s1:signed_sum] 
      	 : signed_sum -> signed_sum :=
Cases s1 of
| (Plus_varlist l1 t1) =>      
     Fix ssm_aux{ssm_aux[s2:signed_sum] : signed_sum :=
           Cases s2 of
      	   | (Plus_varlist l2 t2) =>
	       if (varlist_lt l1 l2)
	       then (Plus_varlist l1 (signed_sum_merge t1 s2))
	       else (Plus_varlist l2 (ssm_aux t2))
      	   | (Minus_varlist l2 t2) =>
      	       if (varlist_eq l1 l2)
	       then (signed_sum_merge t1 t2)
	       else if (varlist_lt l1 l2)
	       then (Plus_varlist l1 (signed_sum_merge t1 s2))
	       else (Minus_varlist l2 (ssm_aux t2))
	   | Nil_varlist => s1
	   end}
| (Minus_varlist l1 t1) =>
     Fix ssm_aux2{ssm_aux2[s2:signed_sum] : signed_sum :=
           Cases s2 of
      	   | (Plus_varlist l2 t2) =>
      	       if (varlist_eq l1 l2)
	       then (signed_sum_merge t1 t2)
	       else if (varlist_lt l1 l2)
	       then (Minus_varlist l1 (signed_sum_merge t1 s2))
	       else (Plus_varlist l2 (ssm_aux2 t2))
      	   | (Minus_varlist l2 t2) =>
	       if (varlist_lt l1 l2)
	       then (Minus_varlist l1 (signed_sum_merge t1 s2))
	       else (Minus_varlist l2 (ssm_aux2 t2))
	   | Nil_varlist => s1
	   end}
| Nil_varlist => [s2]s2
end.

Fixpoint plus_varlist_insert [l1:varlist; s2:signed_sum] 
      : signed_sum :=
  Cases s2 of
  | (Plus_varlist l2 t2) =>
       if (varlist_lt l1 l2)
       then (Plus_varlist l1 s2)
       else (Plus_varlist l2 (plus_varlist_insert l1 t2))
  | (Minus_varlist l2 t2) =>
       if (varlist_eq l1 l2)
       then t2
       else if (varlist_lt l1 l2)
       then (Plus_varlist l1 s2)
       else (Minus_varlist l2 (plus_varlist_insert l1 t2))
  | Nil_varlist => (Plus_varlist l1 Nil_varlist)
  end.

Fixpoint minus_varlist_insert [l1:varlist; s2:signed_sum] 
      : signed_sum :=
  Cases s2 of
  | (Plus_varlist l2 t2) =>
       if (varlist_eq l1 l2)
       then t2
       else if (varlist_lt l1 l2)
       then (Minus_varlist l1 s2)
       else (Plus_varlist l2 (minus_varlist_insert l1 t2))
  | (Minus_varlist l2 t2) =>
       if (varlist_lt l1 l2)
       then (Minus_varlist l1 s2)
       else (Minus_varlist l2 (minus_varlist_insert l1 t2))
  | Nil_varlist => (Minus_varlist l1 Nil_varlist)
  end.

Fixpoint signed_sum_opp [s:signed_sum] : signed_sum :=
  Cases s of
  | (Plus_varlist l2 t2) => (Minus_varlist l2 (signed_sum_opp t2))
  | (Minus_varlist l2 t2) => (Plus_varlist l2 (signed_sum_opp t2))
  | Nil_varlist => Nil_varlist
  end.


Fixpoint plus_sum_scalar [l1:varlist; s2:signed_sum] 
      : signed_sum :=
  Cases s2 of
  | (Plus_varlist l2 t2) => (plus_varlist_insert (varlist_merge l1 l2) 
                                (plus_sum_scalar l1 t2))
  | (Minus_varlist l2 t2) => (minus_varlist_insert (varlist_merge l1 l2) 
                                (plus_sum_scalar l1 t2))
  | Nil_varlist => Nil_varlist
  end.

Fixpoint minus_sum_scalar [l1:varlist; s2:signed_sum] 
      : signed_sum :=
  Cases s2 of
  | (Plus_varlist l2 t2) => (minus_varlist_insert (varlist_merge l1 l2) 
                                (minus_sum_scalar l1 t2))
  | (Minus_varlist l2 t2) => (plus_varlist_insert (varlist_merge l1 l2) 
                                (minus_sum_scalar l1 t2))
  | Nil_varlist => Nil_varlist
  end.

Fixpoint signed_sum_prod [s1:signed_sum] 
      	 : signed_sum -> signed_sum := 
    [s2]Cases s1 of
    | (Plus_varlist l1 t1) =>
	(signed_sum_merge (plus_sum_scalar l1 s2) 
			     (signed_sum_prod t1 s2))
    | (Minus_varlist l1 t1) =>
	(signed_sum_merge (minus_sum_scalar l1 s2) 
			     (signed_sum_prod t1 s2))
    | Nil_varlist => Nil_varlist
    end.

Fixpoint apolynomial_normalize[p:apolynomial] : signed_sum :=
  Cases p of
  | (APvar i) => (Plus_varlist (Cons_var i Nil_var) Nil_varlist)
  | AP1 => (Plus_varlist Nil_var Nil_varlist)
  | AP0 => Nil_varlist
  | (APplus l r) => (signed_sum_merge (apolynomial_normalize l) 
      	       	       	       	       	 (apolynomial_normalize r))
  | (APmult l r) => (signed_sum_prod (apolynomial_normalize l) 
      	       	       	       	        (apolynomial_normalize r))
  | (APopp q) => (signed_sum_opp (apolynomial_normalize q))
  end.


Variable A : Type.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp :A -> A.
Variable Aeq : A -> A -> bool.
Variable vm : (varmap A).
Variable T : (Ring_Theory Aplus Amult Aone Azero Aopp Aeq).

(* Local *) Definition isacs_aux := Fix isacs_aux{isacs_aux [a:A; s:signed_sum] : A :=  
  Cases s of
  | Nil_varlist => a
  | (Plus_varlist l t) => 
	(Aplus a (isacs_aux (interp_vl Amult Aone Azero vm l) t))
  | (Minus_varlist l t) => 
	(Aplus a (isacs_aux (Aopp (interp_vl Amult Aone Azero vm l)) t))
  end}.

Definition interp_sacs [s:signed_sum] : A :=
  Cases s of
  | (Plus_varlist l t) => (isacs_aux (interp_vl Amult Aone Azero vm l) t)
  | (Minus_varlist l t) => 
	(isacs_aux (Aopp (interp_vl Amult Aone Azero vm l)) t)
  | Nil_varlist => Azero
  end.

Fixpoint interp_ap [p:apolynomial] : A :=
  Cases p of
  | (APvar i) => (interp_var Azero vm i)
  | AP0 => Azero
  | AP1 => Aone
  | (APplus l r) => (Aplus (interp_ap l) (interp_ap r))
  | (APmult l r) => (Amult (interp_ap l) (interp_ap r))
  | (APopp q) => (Aopp (interp_ap q))
  end.

Hint Th_plus_sym_T := Resolve (Th_plus_sym T).
Hint Th_plus_assoc_T := Resolve (Th_plus_assoc T).
Hint Th_plus_assoc2_T := Resolve (Th_plus_assoc2 T).
Hint Th_mult_sym_T := Resolve (Th_mult_sym T).
Hint Th_mult_assoc_T := Resolve (Th_mult_assoc T).
Hint Th_mult_assoc2_T := Resolve (Th_mult_assoc2 T).
Hint Th_plus_zero_left_T := Resolve (Th_plus_zero_left T).
Hint Th_plus_zero_left2_T := Resolve (Th_plus_zero_left2 T).
Hint Th_mult_one_left_T := Resolve (Th_mult_one_left T).
Hint Th_mult_one_left2_T := Resolve (Th_mult_one_left2 T).
Hint Th_mult_zero_left_T := Resolve (Th_mult_zero_left T).
Hint Th_mult_zero_left2_T := Resolve (Th_mult_zero_left2 T).
Hint Th_distr_left_T := Resolve (Th_distr_left T).
Hint Th_distr_left2_T := Resolve (Th_distr_left2 T).
Hint Th_plus_reg_left_T := Resolve (Th_plus_reg_left T).
Hint Th_plus_permute_T := Resolve (Th_plus_permute T).
Hint Th_mult_permute_T := Resolve (Th_mult_permute T).
Hint Th_distr_right_T := Resolve (Th_distr_right T).
Hint Th_distr_right2_T := Resolve (Th_distr_right2 T).
Hint Th_mult_zero_right2_T := Resolve (Th_mult_zero_right2 T).
Hint Th_plus_zero_right_T := Resolve (Th_plus_zero_right T).
Hint Th_plus_zero_right2_T := Resolve (Th_plus_zero_right2 T).
Hint Th_mult_one_right_T := Resolve (Th_mult_one_right T).
Hint Th_mult_one_right2_T := Resolve (Th_mult_one_right2 T).
Hint Th_plus_reg_right_T := Resolve (Th_plus_reg_right T).
Hints Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
Hints Immediate T.

Lemma isacs_aux_ok : (x:A)(s:signed_sum)
  (isacs_aux x s)==(Aplus x (interp_sacs s)).
Proof.
  Induction s; Simpl; Intros.
  Trivial.
  Reflexivity.
  Reflexivity.
Save.

Hint rew_isacs_aux : core := Extern 10 (eqT A ? ?) Rewrite isacs_aux_ok.

Tactic Definition Solve1 v v0 H H0 := 
  Simpl; Elim (varlist_lt v v0); Simpl; Rewrite isacs_aux_ok;
    [Rewrite H; Simpl; Auto
    |Simpl in H0; Rewrite H0; Auto ].

Lemma signed_sum_merge_ok : (x,y:signed_sum)
  (interp_sacs (signed_sum_merge x y))
  ==(Aplus (interp_sacs x) (interp_sacs y)).

  Induction x.
  Intro; Simpl; Auto.

  Induction y; Intros.

  Auto.

  Solve1 v v0 H H0.

  Simpl; Generalize (varlist_eq_prop v v0).
  Elim (varlist_eq v v0); Simpl.

  Intro Heq; Rewrite (Heq I).
  Rewrite H.
  Repeat Rewrite isacs_aux_ok.
  Rewrite (Th_plus_permute T). 
  Repeat Rewrite (Th_plus_assoc T).
  Rewrite (Th_plus_sym T (Aopp (interp_vl Amult Aone Azero vm v0))
                         (interp_vl Amult Aone Azero vm v0)).
  Rewrite (Th_opp_def T).
  Rewrite (Th_plus_zero_left T).
  Reflexivity.

  Solve1 v v0 H H0.

  Induction y; Intros.

  Auto.

  Simpl; Generalize (varlist_eq_prop v v0).
  Elim (varlist_eq v v0); Simpl.

  Intro Heq; Rewrite (Heq I).
  Rewrite H.
  Repeat Rewrite isacs_aux_ok.
  Rewrite (Th_plus_permute T). 
  Repeat Rewrite (Th_plus_assoc T).
  Rewrite (Th_opp_def T).
  Rewrite (Th_plus_zero_left T).
  Reflexivity.

  Solve1 v v0 H H0.

  Solve1 v v0 H H0.

Save.

Tactic Definition Solve2 l v H :=
 	Elim (varlist_lt l v); Simpl; Rewrite isacs_aux_ok;
  	[ Auto
  	| Rewrite H; Auto ].

Lemma plus_varlist_insert_ok : (l:varlist)(s:signed_sum)
	(interp_sacs (plus_varlist_insert l s)) 
	== (Aplus (interp_vl  Amult Aone Azero vm l) (interp_sacs s)).
Proof.

  Induction s.
  Trivial.

  Simpl; Intros.
  Solve2 l v H.

  Simpl; Intros.
  Generalize (varlist_eq_prop l v).
  Elim (varlist_eq l v); Simpl.

  Intro Heq; Rewrite (Heq I).
  Repeat Rewrite isacs_aux_ok.
  Repeat Rewrite (Th_plus_assoc T).
  Rewrite (Th_opp_def T).
  Rewrite (Th_plus_zero_left T).
  Reflexivity.

  Solve2 l v H.

Save.

Lemma minus_varlist_insert_ok : (l:varlist)(s:signed_sum)
	(interp_sacs (minus_varlist_insert l s)) 
	== (Aplus (Aopp (interp_vl  Amult Aone Azero vm l)) (interp_sacs s)).
Proof.

  Induction s.
  Trivial.

  Simpl; Intros.
  Generalize (varlist_eq_prop l v).
  Elim (varlist_eq l v); Simpl.

  Intro Heq; Rewrite (Heq I).
  Repeat Rewrite isacs_aux_ok.
  Repeat Rewrite (Th_plus_assoc T).
  Rewrite (Th_plus_sym T (Aopp (interp_vl Amult Aone Azero vm v))
         (interp_vl Amult Aone Azero vm v)).
  Rewrite (Th_opp_def T).
  Auto.

  Simpl; Intros.
  Solve2 l v H.

  Simpl; Intros; Solve2 l v H.

Save.

Lemma signed_sum_opp_ok : (s:signed_sum)
	(interp_sacs (signed_sum_opp s)) 
	== (Aopp (interp_sacs s)).
Proof.

  Induction s; Simpl; Intros.

  Symmetry; Apply (Th_opp_zero T).

  Repeat Rewrite isacs_aux_ok.
  Rewrite H.
  Rewrite (Th_plus_opp_opp T).
  Reflexivity.

  Repeat Rewrite isacs_aux_ok.
  Rewrite H.
  Rewrite <- (Th_plus_opp_opp T).
  Rewrite (Th_opp_opp T).
  Reflexivity.

Save.

Lemma plus_sum_scalar_ok : (l:varlist)(s:signed_sum)
	(interp_sacs (plus_sum_scalar l s)) 
	== (Amult (interp_vl  Amult Aone Azero vm l) (interp_sacs s)).
Proof.

  Induction s.
  Trivial.

  Simpl; Intros.
  Rewrite plus_varlist_insert_ok.
  Rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  Repeat Rewrite isacs_aux_ok.
  Rewrite H.
  Auto.

  Simpl; Intros.
  Rewrite minus_varlist_insert_ok.
  Repeat Rewrite isacs_aux_ok.
  Rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  Rewrite H.
  Rewrite (Th_distr_right T).
  Rewrite <- (Th_opp_mult_right T).
  Reflexivity.

Save.

Lemma minus_sum_scalar_ok : (l:varlist)(s:signed_sum)
	(interp_sacs (minus_sum_scalar l s)) 
	== (Aopp (Amult (interp_vl  Amult Aone Azero vm l) (interp_sacs s))).
Proof.

  Induction s; Simpl; Intros.

  Rewrite (Th_mult_zero_right T); Symmetry; Apply (Th_opp_zero T).

  Simpl; Intros.
  Rewrite minus_varlist_insert_ok.
  Rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  Repeat Rewrite isacs_aux_ok.
  Rewrite H.
  Rewrite (Th_distr_right T).
  Rewrite (Th_plus_opp_opp T).
  Reflexivity.

  Simpl; Intros.
  Rewrite plus_varlist_insert_ok.
  Repeat Rewrite isacs_aux_ok.
  Rewrite (varlist_merge_ok A Aplus Amult Aone Azero Aeq vm T).
  Rewrite H.
  Rewrite (Th_distr_right T).
  Rewrite <- (Th_opp_mult_right T).
  Rewrite <- (Th_plus_opp_opp T).
  Rewrite (Th_opp_opp T).
  Reflexivity.

Save.

Lemma signed_sum_prod_ok : (x,y:signed_sum)
	(interp_sacs (signed_sum_prod x y)) ==
		(Amult (interp_sacs x) (interp_sacs y)).
Proof.

  Induction x.

  Simpl; EAuto 1.

  Intros; Simpl.
  Rewrite signed_sum_merge_ok.
  Rewrite plus_sum_scalar_ok.
  Repeat Rewrite isacs_aux_ok.
  Rewrite H.
  Auto.

  Intros; Simpl.
  Repeat Rewrite isacs_aux_ok.
  Rewrite signed_sum_merge_ok.
  Rewrite minus_sum_scalar_ok.
  Rewrite H.
  Rewrite (Th_distr_left T).
  Rewrite (Th_opp_mult_left T).
  Reflexivity.

Save.

Theorem apolynomial_normalize_ok : (p:apolynomial)
	(interp_sacs (apolynomial_normalize p))==(interp_ap p).
Proof.
  Induction p; Simpl; Auto 1.
  Intros.
    Rewrite signed_sum_merge_ok.
    Rewrite H; Rewrite H0; Reflexivity.
  Intros.
    Rewrite signed_sum_prod_ok.
    Rewrite H; Rewrite H0; Reflexivity.
  Intros.
    Rewrite signed_sum_opp_ok.
    Rewrite H; Reflexivity.
Save.  

End abstract_rings.
