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

Set Implicit Arguments.

Lemma index_eq_prop: (n,m:index)(Is_true (index_eq n m)) -> n=m.
Proof.
  Intros.
  Apply Quote.index_eq_prop.
  Generalize H.
  Case (index_eq n m); Simpl; Trivial; Intros.
  Contradiction.
Save.

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
| Cons_var : index -> varlist -> varlist
.

Inductive canonical_sum : Type := 
| Nil_monom : canonical_sum
| Cons_monom : A -> varlist -> canonical_sum -> canonical_sum
| Cons_varlist : varlist -> canonical_sum -> canonical_sum 
.

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

Fixpoint varlist_eq [x,y:varlist] : bool :=
  Cases x y of
  | Nil_var Nil_var => true
  | (Cons_var i xrest) (Cons_var j yrest) => 
        (andb (index_eq i j) (varlist_eq xrest yrest))
  | _ _ => false
  end.

Fixpoint varlist_lt [x,y:varlist] : bool :=
  Cases x y of 
  | Nil_var (Cons_var _ _) => true
  | (Cons_var i xrest) (Cons_var j yrest) => 
      	if (index_lt i j) then true
        else (andb (index_eq i j) (varlist_lt xrest yrest))
  | _ _ => false
  end.

(* merges two variables lists *)
Fixpoint varlist_merge [l1:varlist] : varlist -> varlist :=
  Cases l1 of	
  | (Cons_var v1 t1) => 
      Fix vm_aux {vm_aux [l2:varlist] : varlist :=
	Cases l2 of
	| (Cons_var v2 t2) => 
		     if (index_lt v1 v2)
		     then (Cons_var v1 (varlist_merge t1 l2))
		     else (Cons_var v2 (vm_aux t2))
	| Nil_var => l1
	end}
  | Nil_var => [l2]l2
  end.

(* returns the sum of two canonical sums  *)
Fixpoint canonical_sum_merge [s1:canonical_sum] 
      	 : canonical_sum -> canonical_sum :=
Cases s1 of
| (Cons_monom c1 l1 t1) =>      
     Fix csm_aux{csm_aux[s2:canonical_sum] : canonical_sum :=
           Cases s2 of
      	   | (Cons_monom c2 l2 t2) =>
      	       if (varlist_eq l1 l2)
	       then (Cons_monom (Aplus c1 c2) l1 
      	       	       	        (canonical_sum_merge t1 t2))
	       else if (varlist_lt l1 l2)
	       then (Cons_monom c1 l1 (canonical_sum_merge t1 s2))
	       else (Cons_monom c2 l2 (csm_aux t2))
      	   | (Cons_varlist l2 t2) =>
      	       if (varlist_eq l1 l2)
	       then (Cons_monom (Aplus c1 Aone) l1 
      	       	       	        (canonical_sum_merge t1 t2))
	       else if (varlist_lt l1 l2)
	       then (Cons_monom c1 l1 (canonical_sum_merge t1 s2))
	       else (Cons_varlist l2 (csm_aux t2))
	   | Nil_monom => s1
	   end}
| (Cons_varlist l1 t1) =>      
     Fix csm_aux2{csm_aux2[s2:canonical_sum] : canonical_sum :=
           Cases s2 of
      	   | (Cons_monom c2 l2 t2) =>
      	       if (varlist_eq l1 l2)
	       then (Cons_monom (Aplus Aone c2) l1 
      	       	       	        (canonical_sum_merge t1 t2))
	       else if (varlist_lt l1 l2)
	       then (Cons_varlist l1 (canonical_sum_merge t1 s2))
	       else (Cons_monom c2 l2 (csm_aux2 t2))
      	   | (Cons_varlist l2 t2) =>
      	       if (varlist_eq l1 l2)
	       then (Cons_monom (Aplus Aone Aone) l1 
      	       	       	        (canonical_sum_merge t1 t2))
	       else if (varlist_lt l1 l2)
	       then (Cons_varlist l1 (canonical_sum_merge t1 s2))
	       else (Cons_varlist l2 (csm_aux2 t2))
	   | Nil_monom => s1
	   end}
| Nil_monom => [s2]s2
end.

(* Insertion of a monom in a canonical sum *)
Fixpoint monom_insert [c1:A; l1:varlist; s2 : canonical_sum] 
      : canonical_sum := 
  Cases s2 of
  | (Cons_monom c2 l2 t2) =>
       if (varlist_eq l1 l2)
       then (Cons_monom (Aplus c1 c2) l1 t2)
       else if (varlist_lt l1 l2)
       then (Cons_monom c1 l1 s2)
       else (Cons_monom c2 l2 (monom_insert c1 l1 t2))
  | (Cons_varlist l2 t2) =>
       if (varlist_eq l1 l2)
       then (Cons_monom (Aplus c1 Aone) l1 t2)
       else if (varlist_lt l1 l2)
       then (Cons_monom c1 l1 s2)
       else (Cons_varlist l2 (monom_insert c1 l1 t2))
  | Nil_monom => (Cons_monom c1 l1 Nil_monom)
  end.

Fixpoint varlist_insert [l1:varlist; s2:canonical_sum] 
      : canonical_sum :=
  Cases s2 of
  | (Cons_monom c2 l2 t2) =>
       if (varlist_eq l1 l2)
       then (Cons_monom (Aplus Aone c2) l1 t2)
       else if (varlist_lt l1 l2)
       then (Cons_varlist l1 s2)
       else (Cons_monom c2 l2 (varlist_insert l1 t2))
  | (Cons_varlist l2 t2) =>
       if (varlist_eq l1 l2)
       then (Cons_monom (Aplus Aone Aone) l1 t2)
       else if (varlist_lt l1 l2)
       then (Cons_varlist l1 s2)
       else (Cons_varlist l2 (varlist_insert l1 t2))
  | Nil_monom => (Cons_varlist l1 Nil_monom)
  end.

(* Computes c0*s *)
Fixpoint canonical_sum_scalar [c0:A; s:canonical_sum] : canonical_sum :=
    Cases s of
    | (Cons_monom c l t) => 
	(Cons_monom (Amult c0 c) l (canonical_sum_scalar c0 t))
    | (Cons_varlist l t) => 
	(Cons_monom c0 l (canonical_sum_scalar c0 t))
    | Nil_monom => Nil_monom
    end.

(* Computes l0*s  *)
Fixpoint canonical_sum_scalar2 [l0:varlist; s:canonical_sum] 
      	       	       	      : canonical_sum :=
    Cases s of
    | (Cons_monom c l t) => 
      	  (monom_insert c (varlist_merge l0 l) (canonical_sum_scalar2 l0 t))
    | (Cons_varlist l t) => 
          (varlist_insert (varlist_merge l0 l) (canonical_sum_scalar2 l0 t))
    | Nil_monom  => Nil_monom
    end.

(* Computes c0*l0*s  *)
Fixpoint canonical_sum_scalar3 [c0:A;l0:varlist; s:canonical_sum] 
      	       	       	      : canonical_sum :=
    Cases s of
    | (Cons_monom c l t) => 
          (monom_insert (Amult c0 c) (varlist_merge l0 l) 
                        (canonical_sum_scalar3 c0 l0 t))
    | (Cons_varlist l t) => 
      	  (monom_insert c0 (varlist_merge l0 l) 
                          (canonical_sum_scalar3 c0 l0 t))
    | Nil_monom  => Nil_monom
    end.

(* returns the product of two canonical sums *) 
Fixpoint canonical_sum_prod [s1:canonical_sum] 
      	 : canonical_sum -> canonical_sum := 
    [s2]Cases s1 of
    | (Cons_monom c1 l1 t1) =>
	(canonical_sum_merge (canonical_sum_scalar3 c1 l1 s2) 
			     (canonical_sum_prod t1 s2))
    | (Cons_varlist l1 t1) =>
	(canonical_sum_merge (canonical_sum_scalar2 l1 s2) 
			     (canonical_sum_prod t1 s2))
    | Nil_monom => Nil_monom
    end.

(* The type to represent concrete semi-ring polynomials *)
Inductive Type spolynomial :=
  SPvar : index -> spolynomial
| SPconst : A -> spolynomial
| SPplus : spolynomial -> spolynomial -> spolynomial
| SPmult : spolynomial -> spolynomial -> spolynomial.

Fixpoint spolynomial_normalize[p:spolynomial] : canonical_sum :=
  Cases p of
  | (SPvar i) => (Cons_varlist (Cons_var i Nil_var) Nil_monom)
  | (SPconst c) => (Cons_monom c Nil_var Nil_monom)
  | (SPplus l r) => (canonical_sum_merge (spolynomial_normalize l) 
      	       	       	       	       	 (spolynomial_normalize r))
  | (SPmult l r) => (canonical_sum_prod (spolynomial_normalize l) 
      	       	       	       	        (spolynomial_normalize r))
  end.

(* Deletion of useless 0 and 1 in canonical sums *)
Fixpoint canonical_sum_simplify [ s:canonical_sum] : canonical_sum :=
  Cases s of
  | (Cons_monom c l t) => 
	 if (Aeq c Azero) 
	 then (canonical_sum_simplify t)
	 else if (Aeq c Aone)
	 then (Cons_varlist l (canonical_sum_simplify t))
	 else (Cons_monom c l (canonical_sum_simplify t))
  | (Cons_varlist l t) => (Cons_varlist l (canonical_sum_simplify t))
  | Nil_monom => Nil_monom
  end.

Definition spolynomial_simplify :=
  [x:spolynomial](canonical_sum_simplify (spolynomial_normalize x)).

(* End definitions. *)

(* Section interpretation. *)

(*** Here a variable map is defined and the interpetation of a spolynom
  acording to a certain variables map. Once again the choosen definition
  is generic and could be changed ****)

Variable vm : (varmap A).

(* Interpretation of list of variables 
 * [x1; ... ; xn ] is interpreted as (find v x1)* ... *(find v xn)
 * The unbound variables are mapped to 0. Normally this case sould
 * never occur. Since we want only to prove correctness theorems, which form
 * is : for any varmap and any spolynom ... this is a safe and pain-saving
 * choice *)
Definition interp_var [i:index] := (varmap_find Azero i vm).

(* Local *) Definition ivl_aux := Fix ivl_aux {ivl_aux[x:index; t:varlist] : A := 
  Cases t of
  | Nil_var => (interp_var x)
  | (Cons_var x' t') => (Amult (interp_var x) (ivl_aux x' t'))
  end}.

Definition interp_vl :=  [l:varlist] 
  Cases l of
  | Nil_var => Aone
  | (Cons_var x t) => (ivl_aux x t)
  end.

(* Local *) Definition interp_m := [c:A][l:varlist] 
  Cases l of
  | Nil_var => c
  | (Cons_var x t) => 
      (Amult c (ivl_aux x t))
  end.

(* Local *) Definition ics_aux := Fix ics_aux{ics_aux[a:A; s:canonical_sum] : A :=  
  Cases s of
  | Nil_monom => a
  | (Cons_varlist l t) => (Aplus a (ics_aux (interp_vl l) t))
  | (Cons_monom c l t) => (Aplus a (ics_aux (interp_m c l) t))
  end}.

(* Interpretation of a canonical sum *)
Definition interp_cs : canonical_sum -> A  := 
  [s]Cases s of 
  | Nil_monom => Azero
  | (Cons_varlist l t) =>
      	(ics_aux (interp_vl l) t)
  | (Cons_monom c l t) =>
      	(ics_aux (interp_m c l) t)
  end.

Fixpoint interp_sp [p:spolynomial] : A :=
  Cases p of
    (SPconst c) => c
  | (SPvar i) => (interp_var i)
  | (SPplus p1 p2) => (Aplus (interp_sp p1) (interp_sp p2))
  | (SPmult p1 p2) => (Amult (interp_sp p1) (interp_sp p2))
  end.


(* End interpretation. *)

Unset Implicit Arguments.

(* Section properties. *)

Variable T : (Semi_Ring_Theory Aplus Amult Aone Azero Aeq).

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
(* Hints Resolve refl_eqT sym_eqT trans_eqT. *)
Hints Immediate T.

Lemma varlist_eq_prop : (x,y:varlist)
  (Is_true (varlist_eq x y))->x==y.
Proof.
  Induction x; Induction y; Contradiction Orelse Try Reflexivity.
  Simpl; Intros.
  Generalize (andb_prop2 ? ? H1); Intros; Elim H2; Intros.
  Rewrite (index_eq_prop H3); Rewrite (H v0 H4); Reflexivity.
Save.

Remark ivl_aux_ok : (v:varlist)(i:index)
  (ivl_aux i v)==(Amult (interp_var i) (interp_vl v)).
Proof.
  Induction v; Simpl; Intros.
  Trivial.
  Rewrite H; Trivial.
Save.

Lemma varlist_merge_ok : (x,y:varlist)
  (interp_vl (varlist_merge x y))
  ==(Amult (interp_vl x) (interp_vl y)).
Proof.
  Induction x.
  Simpl; Trivial.
  Induction y.
  Simpl; Trivial.
  Simpl; Intros.
  Elim (index_lt i i0); Simpl; Intros.

  Repeat Rewrite ivl_aux_ok.
  Rewrite H. Simpl.
  Rewrite ivl_aux_ok.
  EAuto.

  Repeat Rewrite ivl_aux_ok.
  Rewrite H0.
  Rewrite ivl_aux_ok.
  EAuto.
Save.

Remark ics_aux_ok : (x:A)(s:canonical_sum)
  (ics_aux x s)==(Aplus x (interp_cs s)).
Proof.
  Induction s; Simpl; Intros.
  Trivial.
  Reflexivity.
  Reflexivity.
Save.

Remark interp_m_ok : (x:A)(l:varlist)
  (interp_m x l)==(Amult x (interp_vl l)).
Proof.
  NewDestruct l.
  Simpl; Trivial.
  Reflexivity.
Save.

Lemma canonical_sum_merge_ok : (x,y:canonical_sum)
  (interp_cs (canonical_sum_merge x y))
  ==(Aplus (interp_cs x) (interp_cs y)).

Induction x; Simpl.
Trivial.

Induction y; Simpl; Intros.
(* monom and nil *)
EAuto.

(* monom and monom *)
Generalize (varlist_eq_prop v v0).
Elim (varlist_eq v v0).
Intros; Rewrite (H1 I).
Simpl; Repeat Rewrite ics_aux_ok; Rewrite H.
Repeat Rewrite interp_m_ok.
Rewrite (SR_distr_left T).
Repeat Rewrite <- (SR_plus_assoc T).
Apply congr_eqT with f:=(Aplus (Amult a (interp_vl v0))).
Trivial.

Elim (varlist_lt v v0); Simpl.
Repeat Rewrite ics_aux_ok.
Rewrite H; Simpl; Rewrite ics_aux_ok; EAuto.

Rewrite ics_aux_ok; Rewrite H0; Repeat Rewrite ics_aux_ok; Simpl; EAuto.

(* monom and varlist *)
Generalize (varlist_eq_prop v v0).
Elim (varlist_eq v v0).
Intros; Rewrite (H1 I).
Simpl; Repeat Rewrite ics_aux_ok; Rewrite H.
Repeat Rewrite interp_m_ok.
Rewrite (SR_distr_left T).
Repeat Rewrite <- (SR_plus_assoc T).
Apply congr_eqT with f:=(Aplus (Amult a (interp_vl v0))).
Rewrite (SR_mult_one_left T).
Trivial.

Elim (varlist_lt v v0); Simpl.
Repeat Rewrite ics_aux_ok.
Rewrite H; Simpl; Rewrite ics_aux_ok; EAuto.
Rewrite ics_aux_ok; Rewrite H0; Repeat Rewrite ics_aux_ok; Simpl; EAuto.

Induction y; Simpl; Intros.
(* varlist and nil *)
Trivial.

(* varlist and monom *)
Generalize (varlist_eq_prop v v0).
Elim (varlist_eq v v0).
Intros; Rewrite (H1 I).
Simpl; Repeat Rewrite ics_aux_ok; Rewrite H.
Repeat Rewrite interp_m_ok.
Rewrite (SR_distr_left T).
Repeat Rewrite <- (SR_plus_assoc T).
Rewrite (SR_mult_one_left T).
Apply congr_eqT with f:=(Aplus (interp_vl v0)).
Trivial.

Elim (varlist_lt v v0); Simpl.
Repeat Rewrite ics_aux_ok.
Rewrite H; Simpl; Rewrite ics_aux_ok; EAuto.
Rewrite ics_aux_ok; Rewrite H0; Repeat Rewrite ics_aux_ok; Simpl; EAuto.

(* varlist and varlist *)
Generalize (varlist_eq_prop v v0).
Elim (varlist_eq v v0).
Intros; Rewrite (H1 I).
Simpl; Repeat Rewrite ics_aux_ok; Rewrite H.
Repeat Rewrite interp_m_ok.
Rewrite (SR_distr_left T).
Repeat Rewrite <- (SR_plus_assoc T).
Rewrite (SR_mult_one_left T).
Apply congr_eqT with f:=(Aplus (interp_vl v0)).
Trivial.

Elim (varlist_lt v v0); Simpl.
Repeat Rewrite ics_aux_ok.
Rewrite H; Simpl; Rewrite ics_aux_ok; EAuto.
Rewrite ics_aux_ok; Rewrite H0; Repeat Rewrite ics_aux_ok; Simpl; EAuto.
Save.

Lemma monom_insert_ok: (a:A)(l:varlist)(s:canonical_sum)
  (interp_cs (monom_insert a l s)) 
  == (Aplus (Amult a (interp_vl l)) (interp_cs s)).
Intros; Generalize s; Induction s0.

Simpl; Rewrite interp_m_ok; Trivial.

Simpl; Intros.
Generalize (varlist_eq_prop  l v); Elim (varlist_eq l v).
Intro Hr; Rewrite (Hr I); Simpl; Rewrite interp_m_ok; 
  Repeat Rewrite ics_aux_ok; Rewrite interp_m_ok;
  Rewrite (SR_distr_left T); EAuto.
Elim (varlist_lt l v); Simpl; 
[ Repeat Rewrite interp_m_ok; Rewrite ics_aux_ok; EAuto
| Repeat Rewrite interp_m_ok; Rewrite ics_aux_ok;
  Rewrite H; Rewrite ics_aux_ok; EAuto].

Simpl; Intros.
Generalize (varlist_eq_prop  l v); Elim (varlist_eq l v).
Intro Hr; Rewrite (Hr I); Simpl;  Rewrite interp_m_ok; 
  Repeat Rewrite ics_aux_ok; 
  Rewrite (SR_distr_left T); Rewrite (SR_mult_one_left T); EAuto.
Elim (varlist_lt l v); Simpl; 
[ Repeat Rewrite interp_m_ok; Rewrite ics_aux_ok; EAuto
| Repeat Rewrite interp_m_ok; Rewrite ics_aux_ok;
  Rewrite H; Rewrite ics_aux_ok; EAuto].
Save.

Lemma varlist_insert_ok :
 (l:varlist)(s:canonical_sum)
  (interp_cs (varlist_insert l s)) 
  == (Aplus (interp_vl l) (interp_cs s)).
Intros; Generalize s; Induction s0.

Simpl; Trivial.

Simpl; Intros.
Generalize (varlist_eq_prop  l v); Elim (varlist_eq l v).
Intro Hr; Rewrite (Hr I); Simpl; Rewrite interp_m_ok; 
  Repeat Rewrite ics_aux_ok; Rewrite interp_m_ok;
  Rewrite (SR_distr_left T); Rewrite (SR_mult_one_left T); EAuto.
Elim (varlist_lt l v); Simpl; 
[ Repeat Rewrite interp_m_ok; Rewrite ics_aux_ok; EAuto
| Repeat Rewrite interp_m_ok; Rewrite ics_aux_ok;
  Rewrite H; Rewrite ics_aux_ok; EAuto].

Simpl; Intros.
Generalize (varlist_eq_prop  l v); Elim (varlist_eq l v).
Intro Hr; Rewrite (Hr I); Simpl;  Rewrite interp_m_ok; 
  Repeat Rewrite ics_aux_ok; 
  Rewrite (SR_distr_left T); Rewrite (SR_mult_one_left T); EAuto.
Elim (varlist_lt l v); Simpl; 
[ Repeat Rewrite interp_m_ok; Rewrite ics_aux_ok; EAuto
| Repeat Rewrite interp_m_ok; Rewrite ics_aux_ok;
  Rewrite H; Rewrite ics_aux_ok; EAuto].
Save.

Lemma canonical_sum_scalar_ok : (a:A)(s:canonical_sum)
  (interp_cs (canonical_sum_scalar a s))
  ==(Amult a (interp_cs s)).
Induction s.
Simpl; EAuto.

Simpl; Intros.
Repeat Rewrite ics_aux_ok.
Repeat Rewrite interp_m_ok.
Rewrite H.
Rewrite (SR_distr_right T).
Repeat Rewrite <- (SR_mult_assoc T).
Reflexivity.

Simpl; Intros.
Repeat Rewrite ics_aux_ok.
Repeat Rewrite interp_m_ok.
Rewrite H.
Rewrite (SR_distr_right T).
Repeat Rewrite <- (SR_mult_assoc T).
Reflexivity.
Save.

Lemma canonical_sum_scalar2_ok : (l:varlist; s:canonical_sum)
  (interp_cs (canonical_sum_scalar2 l s))
   ==(Amult (interp_vl l) (interp_cs s)).
Induction s.
Simpl; Trivial.

Simpl; Intros.
Rewrite monom_insert_ok.
Repeat Rewrite ics_aux_ok.
Repeat Rewrite interp_m_ok.
Rewrite H.
Rewrite varlist_merge_ok.
Repeat Rewrite (SR_distr_right T). 
Repeat Rewrite <- (SR_mult_assoc T).
Repeat Rewrite <- (SR_plus_assoc T).
Rewrite (SR_mult_permute T  a (interp_vl l) (interp_vl v)).
Reflexivity.

Simpl; Intros.
Rewrite varlist_insert_ok.
Repeat Rewrite ics_aux_ok.
Repeat Rewrite interp_m_ok.
Rewrite H.
Rewrite varlist_merge_ok.
Repeat Rewrite (SR_distr_right T). 
Repeat Rewrite <- (SR_mult_assoc T).
Repeat Rewrite <- (SR_plus_assoc T).
Reflexivity.
Save.

Lemma canonical_sum_scalar3_ok : (c:A; l:varlist; s:canonical_sum)
  (interp_cs (canonical_sum_scalar3 c l s))
   ==(Amult c (Amult (interp_vl l) (interp_cs s))).
Induction s.
Simpl; Repeat Rewrite (SR_mult_zero_right T); Reflexivity.

Simpl; Intros.
Rewrite monom_insert_ok.
Repeat Rewrite ics_aux_ok.
Repeat Rewrite interp_m_ok.
Rewrite H.
Rewrite varlist_merge_ok.
Repeat Rewrite (SR_distr_right T). 
Repeat Rewrite <- (SR_mult_assoc T).
Repeat Rewrite <- (SR_plus_assoc T).
Rewrite (SR_mult_permute T  a (interp_vl l) (interp_vl v)).
Reflexivity.

Simpl; Intros.
Rewrite monom_insert_ok.
Repeat Rewrite ics_aux_ok.
Repeat Rewrite interp_m_ok.
Rewrite H.
Rewrite varlist_merge_ok.
Repeat Rewrite (SR_distr_right T). 
Repeat Rewrite <- (SR_mult_assoc T).
Repeat Rewrite <- (SR_plus_assoc T).
Rewrite (SR_mult_permute T c (interp_vl l) (interp_vl v)).
Reflexivity.
Save.

Lemma canonical_sum_prod_ok : (x,y:canonical_sum)
  (interp_cs (canonical_sum_prod x y))
  ==(Amult (interp_cs x) (interp_cs y)).
Induction x; Simpl; Intros.
Trivial.

Rewrite canonical_sum_merge_ok.
Rewrite canonical_sum_scalar3_ok.
Rewrite ics_aux_ok.
Rewrite interp_m_ok.
Rewrite H.
Rewrite (SR_mult_assoc T a (interp_vl v) (interp_cs y)).
Symmetry.
EAuto.

Rewrite canonical_sum_merge_ok.
Rewrite canonical_sum_scalar2_ok.
Rewrite ics_aux_ok.
Rewrite H.
Trivial.
Save.

Theorem spolynomial_normalize_ok : (p:spolynomial)
  (interp_cs (spolynomial_normalize p)) == (interp_sp p).
Induction p; Simpl; Intros.

Reflexivity.
Reflexivity.

Rewrite canonical_sum_merge_ok.
Rewrite H; Rewrite H0.
Reflexivity.

Rewrite canonical_sum_prod_ok.
Rewrite H; Rewrite H0.
Reflexivity.
Save.

Lemma canonical_sum_simplify_ok : (s:canonical_sum)
  (interp_cs (canonical_sum_simplify s)) == (interp_cs s).
Induction s.

Reflexivity.

(* cons_monom *)
Simpl; Intros.
Generalize (SR_eq_prop T 8!a 9!Azero).
Elim (Aeq a Azero).
Intro Heq; Rewrite (Heq I).
Rewrite H.
Rewrite ics_aux_ok.
Rewrite interp_m_ok.
Rewrite (SR_mult_zero_left T).
Trivial.

Intros; Simpl.
Generalize (SR_eq_prop T 8!a 9!Aone).
Elim (Aeq a Aone).
Intro Heq; Rewrite (Heq I).
Simpl.
Repeat Rewrite ics_aux_ok.
Rewrite interp_m_ok.
Rewrite H.
Rewrite (SR_mult_one_left T).
Reflexivity.

Simpl.
Repeat Rewrite ics_aux_ok.
Rewrite interp_m_ok.
Rewrite H.
Reflexivity.

(* cons_varlist *)
Simpl; Intros.
Repeat Rewrite ics_aux_ok.
Rewrite H.
Reflexivity.

Save.

Theorem spolynomial_simplify_ok : (p:spolynomial)
  (interp_cs (spolynomial_simplify p)) == (interp_sp p).
Intro.
Unfold spolynomial_simplify.
Rewrite canonical_sum_simplify_ok.
Apply spolynomial_normalize_ok.
Save.

(* End properties. *)
End semi_rings.

Implicits Cons_varlist.
Implicits Cons_monom.
Implicits SPconst.
Implicits SPplus.
Implicits SPmult.

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
Variable vm : (varmap A).
Variable T : (Ring_Theory Aplus Amult Aone Azero Aopp Aeq).

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
Hint Th_mult_zero_right_T := Resolve (Th_mult_zero_right T).
Hint Th_mult_zero_right2_T := Resolve (Th_mult_zero_right2 T).
Hint Th_plus_zero_right_T := Resolve (Th_plus_zero_right T).
Hint Th_plus_zero_right2_T := Resolve (Th_plus_zero_right2 T).
Hint Th_mult_one_right_T := Resolve (Th_mult_one_right T).
Hint Th_mult_one_right2_T := Resolve (Th_mult_one_right2 T).
Hint Th_plus_reg_right_T := Resolve (Th_plus_reg_right T).
Hints Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
Hints Immediate T.

(*** Definitions *)

Inductive Type polynomial := 
  Pvar : index -> polynomial
| Pconst : A -> polynomial
| Pplus : polynomial -> polynomial -> polynomial
| Pmult : polynomial -> polynomial -> polynomial
| Popp : polynomial -> polynomial.

Fixpoint polynomial_normalize [x:polynomial] : (canonical_sum A) :=
  Cases x of
    (Pplus l r) => (canonical_sum_merge Aplus Aone
      	       	       	       	(polynomial_normalize l) 
                                (polynomial_normalize r))
  | (Pmult l r) => (canonical_sum_prod Aplus Amult Aone 
      	       	       	       	(polynomial_normalize l)
                                (polynomial_normalize r))
  | (Pconst c)  => (Cons_monom c Nil_var (Nil_monom A))
  | (Pvar i)    => (Cons_varlist (Cons_var i Nil_var) (Nil_monom A))
  | (Popp p)    => (canonical_sum_scalar3 Aplus Amult Aone
                                     (Aopp Aone) Nil_var
                                     (polynomial_normalize p))
  end.

Definition polynomial_simplify :=
  [x:polynomial](canonical_sum_simplify Aone Azero Aeq 
      	       	       	(polynomial_normalize x)).

Fixpoint spolynomial_of [x:polynomial] : (spolynomial A) :=
  Cases x of 
    (Pplus l r) => (SPplus (spolynomial_of l) (spolynomial_of r))
  | (Pmult l r) => (SPmult (spolynomial_of l) (spolynomial_of r))
  | (Pconst c)  => (SPconst c)
  | (Pvar i)    => (SPvar A i)
  | (Popp p)    => (SPmult (SPconst (Aopp Aone)) (spolynomial_of p))
  end.

(*** Interpretation *)

Fixpoint interp_p [p:polynomial] : A :=
  Cases p of
    (Pconst c)    => c
  | (Pvar i)      => (varmap_find Azero i vm)
  | (Pplus p1 p2) => (Aplus (interp_p p1) (interp_p p2))
  | (Pmult p1 p2) => (Amult (interp_p p1) (interp_p p2))
  | (Popp p1)     => (Aopp (interp_p p1))
  end.

(*** Properties *)

Unset Implicit Arguments.

Lemma spolynomial_of_ok : (p:polynomial)
  (interp_p p)==(interp_sp Aplus Amult Azero vm (spolynomial_of p)).
Induction p; Reflexivity Orelse (Simpl; Intros).
Rewrite H; Rewrite H0; Reflexivity.
Rewrite H; Rewrite H0; Reflexivity.
Rewrite H.
Rewrite (Th_opp_mult_left2 T).
Rewrite (Th_mult_one_left T).
Reflexivity.
Save.

Theorem polynomial_normalize_ok : (p:polynomial)
  (polynomial_normalize p)
  ==(spolynomial_normalize Aplus Amult Aone (spolynomial_of p)).
Induction p; Reflexivity Orelse (Simpl; Intros).
Rewrite H; Rewrite H0; Reflexivity.
Rewrite H; Rewrite H0; Reflexivity.
Rewrite H; Simpl.
Elim (canonical_sum_scalar3 Aplus Amult Aone (Aopp Aone) Nil_var
     (spolynomial_normalize Aplus Amult Aone (spolynomial_of p0)));
[ Reflexivity
| Simpl; Intros; Rewrite H0; Reflexivity
| Simpl; Intros; Rewrite H0; Reflexivity ].
Save.

Theorem polynomial_simplify_ok : (p:polynomial)
  (interp_cs Aplus Amult Aone Azero vm (polynomial_simplify p))
  ==(interp_p p).
Intro.
Unfold polynomial_simplify.
Rewrite spolynomial_of_ok.
Rewrite polynomial_normalize_ok.
Rewrite (canonical_sum_simplify_ok A Aplus Amult Aone Azero Aeq vm T).
Rewrite (spolynomial_normalize_ok A Aplus Amult Aone Azero Aeq vm T).
Reflexivity.
Save.

End rings.

V8Infix "+" Pplus : ring_scope.
V8Infix "*" Pmult : ring_scope.
V8Notation "- x" := (Popp x) : ring_scope.
V8Notation "[ x ]" := (Pvar x) (at level 1) : ring_scope.

Delimits Scope ring_scope with ring.
