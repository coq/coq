(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Setoid_ring_theory.
Require Quote.

Set Implicit Arguments.

Lemma index_eq_prop: (n,m:index)(Is_true (index_eq n m)) -> n=m.
Proof.
  Induction n; Induction m; Simpl; Try (Reflexivity Orelse Contradiction).
  Intros; Rewrite (H i0); Trivial.
  Intros; Rewrite (H i0); Trivial.
Save.

Section setoid.

Variable A : Type.
Variable Aequiv : A -> A -> Prop.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp : A -> A.
Variable Aeq : A -> A -> bool.

Variable S : (Setoid_Theory A Aequiv).

Add Setoid A Aequiv S.

Variable plus_morph : (a,a0,a1,a2:A)
 (Aequiv a a0)->(Aequiv a1 a2)->(Aequiv (Aplus a a1) (Aplus a0 a2)).
Variable mult_morph : (a,a0,a1,a2:A)
 (Aequiv a a0)->(Aequiv a1 a2)->(Aequiv (Amult a a1) (Amult a0 a2)).
Variable opp_morph : (a,a0:A)
 (Aequiv a a0)->(Aequiv (Aopp a) (Aopp a0)).

Add Morphism Aplus : Aplus_ext.
Exact plus_morph.
Save.

Add Morphism Amult : Amult_ext.
Exact mult_morph.
Save.

Add Morphism Aopp : Aopp_ext.
Exact opp_morph.
Save.

Local equiv_refl := (Seq_refl A Aequiv S).
Local equiv_sym := (Seq_sym A Aequiv S).
Local equiv_trans := (Seq_trans A Aequiv S).

Hints Resolve equiv_refl equiv_trans.
Hints Immediate equiv_sym.

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

(* The type to represent concrete semi-setoid-ring polynomials *)

Inductive Type setspolynomial :=
  SetSPvar : index -> setspolynomial
| SetSPconst : A -> setspolynomial
| SetSPplus : setspolynomial -> setspolynomial -> setspolynomial
| SetSPmult : setspolynomial -> setspolynomial -> setspolynomial.

Fixpoint setspolynomial_normalize [p:setspolynomial] : canonical_sum :=
 Cases p of
 | (SetSPplus l r) => (canonical_sum_merge (setspolynomial_normalize l) (setspolynomial_normalize r))
 | (SetSPmult l r) => (canonical_sum_prod (setspolynomial_normalize l) (setspolynomial_normalize r))
 | (SetSPconst c)  => (Cons_monom c Nil_var Nil_monom)
 | (SetSPvar i)    => (Cons_varlist (Cons_var i Nil_var) Nil_monom)
 end.

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

Definition setspolynomial_simplify :=
  [x:setspolynomial] (canonical_sum_simplify (setspolynomial_normalize x)).

Variable vm : (varmap A).

Definition interp_var [i:index] := (varmap_find Azero i vm).

Definition ivl_aux := Fix ivl_aux {ivl_aux[x:index; t:varlist] : A := 
  Cases t of
  | Nil_var => (interp_var x)
  | (Cons_var x' t') => (Amult (interp_var x) (ivl_aux x' t'))
  end}.

Definition interp_vl :=  [l:varlist] 
  Cases l of
  | Nil_var => Aone
  | (Cons_var x t) => (ivl_aux x t)
  end.

Definition interp_m := [c:A][l:varlist] 
  Cases l of
  | Nil_var => c
  | (Cons_var x t) => 
      (Amult c (ivl_aux x t))
  end.

Definition ics_aux := Fix ics_aux{ics_aux[a:A; s:canonical_sum] : A :=  
  Cases s of
  | Nil_monom => a
  | (Cons_varlist l t) => (Aplus a (ics_aux (interp_vl l) t))
  | (Cons_monom c l t) => (Aplus a (ics_aux (interp_m c l) t))
  end}.

Definition interp_setcs : canonical_sum -> A  := 
  [s]Cases s of 
  | Nil_monom => Azero
  | (Cons_varlist l t) =>
      	(ics_aux (interp_vl l) t)
  | (Cons_monom c l t) =>
      	(ics_aux (interp_m c l) t)
  end.

Fixpoint interp_setsp [p:setspolynomial] : A :=
 Cases p of
 | (SetSPconst c) => c
 | (SetSPvar i) => (interp_var i)
 | (SetSPplus p1 p2) => (Aplus (interp_setsp p1) (interp_setsp p2))
 | (SetSPmult p1 p2) => (Amult (interp_setsp p1) (interp_setsp p2))
 end.

(* End interpretation. *)

Unset Implicit Arguments.

(* Section properties. *)

Variable T : (Semi_Setoid_Ring_Theory Aequiv Aplus Amult Aone Azero Aeq).

Hint SSR_plus_sym_T := Resolve (SSR_plus_sym T).
Hint SSR_plus_assoc_T := Resolve (SSR_plus_assoc T).
Hint SSR_plus_assoc2_T := Resolve (SSR_plus_assoc2 S T).
Hint SSR_mult_sym_T := Resolve (SSR_mult_sym T).
Hint SSR_mult_assoc_T := Resolve (SSR_mult_assoc T).
Hint SSR_mult_assoc2_T := Resolve (SSR_mult_assoc2 S T).
Hint SSR_plus_zero_left_T := Resolve (SSR_plus_zero_left T).
Hint SSR_plus_zero_left2_T := Resolve (SSR_plus_zero_left2 S T).
Hint SSR_mult_one_left_T := Resolve (SSR_mult_one_left T).
Hint SSR_mult_one_left2_T := Resolve (SSR_mult_one_left2 S T).
Hint SSR_mult_zero_left_T := Resolve (SSR_mult_zero_left T).
Hint SSR_mult_zero_left2_T := Resolve (SSR_mult_zero_left2 S T).
Hint SSR_distr_left_T := Resolve (SSR_distr_left T).
Hint SSR_distr_left2_T := Resolve (SSR_distr_left2 S T).
Hint SSR_plus_reg_left_T := Resolve (SSR_plus_reg_left T).
Hint SSR_plus_permute_T := Resolve (SSR_plus_permute S plus_morph T).
Hint SSR_mult_permute_T := Resolve (SSR_mult_permute S mult_morph T).
Hint SSR_distr_right_T := Resolve (SSR_distr_right S plus_morph T).
Hint SSR_distr_right2_T := Resolve (SSR_distr_right2 S plus_morph T).
Hint SSR_mult_zero_right_T := Resolve (SSR_mult_zero_right S T).
Hint SSR_mult_zero_right2_T := Resolve (SSR_mult_zero_right2 S T).
Hint SSR_plus_zero_right_T := Resolve (SSR_plus_zero_right S T).
Hint SSR_plus_zero_right2_T := Resolve (SSR_plus_zero_right2 S T).
Hint SSR_mult_one_right_T := Resolve (SSR_mult_one_right S T).
Hint SSR_mult_one_right2_T := Resolve (SSR_mult_one_right2 S T).
Hint SSR_plus_reg_right_T := Resolve (SSR_plus_reg_right S T).
Hints Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
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
  (Aequiv (ivl_aux i v) (Amult (interp_var i) (interp_vl v))).
Proof.
  Induction v; Simpl; Intros.
  Trivial.
  Rewrite (H i); Trivial.
Save.

Lemma varlist_merge_ok : (x,y:varlist)
  (Aequiv (interp_vl (varlist_merge x y)) (Amult (interp_vl x) (interp_vl y))).
Proof.
  Induction x.
  Simpl; Trivial.
  Induction y.
  Simpl; Trivial.
  Simpl; Intros.
  Elim (index_lt i i0); Simpl; Intros.

  Rewrite (ivl_aux_ok v i).
  Rewrite (ivl_aux_ok v0 i0).
  Rewrite (ivl_aux_ok (varlist_merge v (Cons_var i0 v0)) i).
  Rewrite (H (Cons_var i0 v0)).
  Simpl.
  Rewrite (ivl_aux_ok v0 i0).
  EAuto.

  Rewrite (ivl_aux_ok v i).
  Rewrite (ivl_aux_ok v0 i0).
  Rewrite (ivl_aux_ok
                 (Fix vm_aux
                    {vm_aux [l2:varlist] : varlist :=
                       Cases (l2) of
                         Nil_var => (Cons_var i v)
                       | (Cons_var v2 t2) => 
                          (if (index_lt i v2)
                           then (Cons_var i (varlist_merge v l2))
                           else (Cons_var v2 (vm_aux t2)))
                       end} v0) i0).
  Rewrite H0.
  Rewrite (ivl_aux_ok v i).
  EAuto.
Save.

Remark ics_aux_ok : (x:A)(s:canonical_sum)
  (Aequiv (ics_aux x s) (Aplus x (interp_setcs s))).
Proof.
 Induction s; Simpl; Intros;Trivial.
Save.

Remark interp_m_ok : (x:A)(l:varlist)
  (Aequiv (interp_m x l) (Amult x (interp_vl l))).
Proof.
  NewDestruct l;Trivial.
Save.

Hint ivl_aux_ok_ := Resolve ivl_aux_ok.
Hint ics_aux_ok_ := Resolve ics_aux_ok.
Hint interp_m_ok_ := Resolve interp_m_ok.

(* Hints Resolve ivl_aux_ok ics_aux_ok interp_m_ok. *)

Lemma canonical_sum_merge_ok : (x,y:canonical_sum)
  (Aequiv (interp_setcs (canonical_sum_merge x y))
  (Aplus (interp_setcs x) (interp_setcs y))).
Proof.
Induction x; Simpl.
Trivial.

Induction y; Simpl; Intros.
EAuto.

Generalize (varlist_eq_prop v v0).
Elim (varlist_eq v v0).
Intros; Rewrite (H1 I).
Simpl.
Rewrite (ics_aux_ok (interp_m a v0) c).
Rewrite (ics_aux_ok (interp_m a0 v0) c0).
Rewrite (ics_aux_ok (interp_m (Aplus a a0) v0)
                 (canonical_sum_merge c c0)).
Rewrite (H c0).
Rewrite (interp_m_ok (Aplus a a0) v0).
Rewrite (interp_m_ok a v0).
Rewrite (interp_m_ok a0 v0).
Setoid_replace (Amult (Aplus a a0) (interp_vl v0))
 with (Aplus (Amult a (interp_vl v0)) (Amult a0 (interp_vl v0))).
Setoid_replace (Aplus
                 (Aplus (Amult a (interp_vl v0))
                   (Amult a0 (interp_vl v0)))
                 (Aplus (interp_setcs c) (interp_setcs c0)))
 with (Aplus (Amult a (interp_vl v0))
        (Aplus (Amult a0 (interp_vl v0))
          (Aplus (interp_setcs c) (interp_setcs c0)))).
Setoid_replace (Aplus (Aplus (Amult a (interp_vl v0)) (interp_setcs c))
                 (Aplus (Amult a0 (interp_vl v0)) (interp_setcs c0)))
 with (Aplus (Amult a (interp_vl v0))
        (Aplus (interp_setcs c)
          (Aplus (Amult a0 (interp_vl v0)) (interp_setcs c0)))).
Auto.

Elim (varlist_lt v v0); Simpl.
Intro.
Rewrite (ics_aux_ok (interp_m a v)
                 (canonical_sum_merge c (Cons_monom a0 v0 c0))).
Rewrite (ics_aux_ok (interp_m a v) c).
Rewrite (ics_aux_ok (interp_m a0 v0) c0).
Rewrite (H (Cons_monom a0 v0 c0)); Simpl.
Rewrite (ics_aux_ok (interp_m a0 v0) c0); Auto.

Intro.
Rewrite (ics_aux_ok (interp_m a0 v0)
                 (Fix csm_aux
                    {csm_aux [s2:canonical_sum] : canonical_sum :=
                       Cases (s2) of
                         Nil_monom => (Cons_monom a v c)
                       | (Cons_monom c2 l2 t2) => 
                          (if (varlist_eq v l2)
                           then
                            (Cons_monom (Aplus a c2) v
                              (canonical_sum_merge c t2))
                           else
                            (if (varlist_lt v l2)
                             then
                              (Cons_monom a v
                                (canonical_sum_merge c s2))
                             else (Cons_monom c2 l2 (csm_aux t2))))
                       | (Cons_varlist l2 t2) => 
                          (if (varlist_eq v l2)
                           then
                            (Cons_monom (Aplus a Aone) v
                              (canonical_sum_merge c t2))
                           else
                            (if (varlist_lt v l2)
                             then
                              (Cons_monom a v
                                (canonical_sum_merge c s2))
                             else (Cons_varlist l2 (csm_aux t2))))
                       end} c0)).
Rewrite H0.
Rewrite (ics_aux_ok (interp_m a v) c);
Rewrite (ics_aux_ok (interp_m a0 v0) c0); Simpl; Auto.

Generalize (varlist_eq_prop v v0).
Elim (varlist_eq v v0).
Intros; Rewrite (H1 I).
Simpl.
Rewrite (ics_aux_ok (interp_m (Aplus a Aone) v0)
                 (canonical_sum_merge c c0));
Rewrite (ics_aux_ok (interp_m a v0) c);
Rewrite (ics_aux_ok (interp_vl v0) c0).
Rewrite (H c0).
Rewrite (interp_m_ok (Aplus a Aone) v0).
Rewrite (interp_m_ok a v0).
Setoid_replace (Amult (Aplus a Aone) (interp_vl v0))
 with (Aplus (Amult a (interp_vl v0)) (Amult Aone (interp_vl v0))).
Setoid_replace (Aplus
                 (Aplus (Amult a (interp_vl v0))
                   (Amult Aone (interp_vl v0)))
                 (Aplus (interp_setcs c) (interp_setcs c0)))
 with (Aplus (Amult a (interp_vl v0))
        (Aplus (Amult Aone (interp_vl v0))
          (Aplus (interp_setcs c) (interp_setcs c0)))).
Setoid_replace (Aplus (Aplus (Amult a (interp_vl v0)) (interp_setcs c))
                 (Aplus (interp_vl v0) (interp_setcs c0)))
 with (Aplus (Amult a (interp_vl v0))
        (Aplus (interp_setcs c) (Aplus (interp_vl v0) (interp_setcs c0)))).
Setoid_replace (Amult Aone (interp_vl v0)) with (interp_vl v0).
Auto.

Elim (varlist_lt v v0); Simpl.
Intro.
Rewrite (ics_aux_ok (interp_m a v)
                 (canonical_sum_merge c (Cons_varlist v0 c0)));
Rewrite (ics_aux_ok (interp_m a v) c);
Rewrite (ics_aux_ok (interp_vl v0) c0).
Rewrite (H (Cons_varlist v0 c0)); Simpl.
Rewrite (ics_aux_ok (interp_vl v0) c0).
Auto.

Intro.
Rewrite (ics_aux_ok (interp_vl v0)
                 (Fix csm_aux
                    {csm_aux [s2:canonical_sum] : canonical_sum :=
                       Cases (s2) of
                         Nil_monom => (Cons_monom a v c)
                       | (Cons_monom c2 l2 t2) => 
                          (if (varlist_eq v l2)
                           then
                            (Cons_monom (Aplus a c2) v
                              (canonical_sum_merge c t2))
                           else
                            (if (varlist_lt v l2)
                             then
                              (Cons_monom a v
                                (canonical_sum_merge c s2))
                             else (Cons_monom c2 l2 (csm_aux t2))))
                       | (Cons_varlist l2 t2) => 
                          (if (varlist_eq v l2)
                           then
                            (Cons_monom (Aplus a Aone) v
                              (canonical_sum_merge c t2))
                           else
                            (if (varlist_lt v l2)
                             then
                              (Cons_monom a v
                                (canonical_sum_merge c s2))
                             else (Cons_varlist l2 (csm_aux t2))))
                       end} c0)); Rewrite H0.
Rewrite (ics_aux_ok (interp_m a v) c);
Rewrite (ics_aux_ok (interp_vl v0) c0); Simpl.
Auto.

Induction y; Simpl; Intros.
Trivial.

Generalize (varlist_eq_prop v v0).
Elim (varlist_eq v v0).
Intros; Rewrite (H1 I).
Simpl.
Rewrite (ics_aux_ok (interp_m (Aplus Aone a) v0)
                 (canonical_sum_merge c c0));
Rewrite (ics_aux_ok (interp_vl v0) c);
Rewrite (ics_aux_ok (interp_m a v0) c0); Rewrite (
H c0).
Rewrite (interp_m_ok (Aplus Aone a) v0);
Rewrite (interp_m_ok a v0).
Setoid_replace (Amult (Aplus Aone a) (interp_vl v0))
 with (Aplus (Amult Aone (interp_vl v0)) (Amult a (interp_vl v0)));
Setoid_replace (Aplus
                 (Aplus (Amult Aone (interp_vl v0))
                   (Amult a (interp_vl v0)))
                 (Aplus (interp_setcs c) (interp_setcs c0)))
 with (Aplus (Amult Aone (interp_vl v0))
        (Aplus (Amult a (interp_vl v0))
          (Aplus (interp_setcs c) (interp_setcs c0))));
Setoid_replace (Aplus (Aplus (interp_vl v0) (interp_setcs c))
                 (Aplus (Amult a (interp_vl v0)) (interp_setcs c0)))
 with (Aplus (interp_vl v0)
        (Aplus (interp_setcs c)
          (Aplus (Amult a (interp_vl v0)) (interp_setcs c0)))).
Auto.

Elim (varlist_lt v v0); Simpl; Intros.
Rewrite (ics_aux_ok (interp_vl v)
                 (canonical_sum_merge c (Cons_monom a v0 c0)));
Rewrite (ics_aux_ok (interp_vl v) c);
Rewrite (ics_aux_ok (interp_m a v0) c0).
Rewrite (H (Cons_monom a v0 c0)); Simpl.
Rewrite (ics_aux_ok (interp_m a v0) c0); Auto.

Rewrite (ics_aux_ok (interp_m a v0)
                 (Fix csm_aux2
                    {csm_aux2 [s2:canonical_sum] : canonical_sum :=
                       Cases (s2) of
                         Nil_monom => (Cons_varlist v c)
                       | (Cons_monom c2 l2 t2) => 
                          (if (varlist_eq v l2)
                           then
                            (Cons_monom (Aplus Aone c2) v
                              (canonical_sum_merge c t2))
                           else
                            (if (varlist_lt v l2)
                             then
                              (Cons_varlist v
                                (canonical_sum_merge c s2))
                             else (Cons_monom c2 l2 (csm_aux2 t2))))
                       | (Cons_varlist l2 t2) => 
                          (if (varlist_eq v l2)
                           then
                            (Cons_monom (Aplus Aone Aone) v
                              (canonical_sum_merge c t2))
                           else
                            (if (varlist_lt v l2)
                             then
                              (Cons_varlist v
                                (canonical_sum_merge c s2))
                             else (Cons_varlist l2 (csm_aux2 t2))))
                       end} c0)); Rewrite H0.
Rewrite (ics_aux_ok (interp_vl v) c);
Rewrite (ics_aux_ok (interp_m a v0) c0); Simpl; Auto.

Generalize (varlist_eq_prop v v0).
Elim (varlist_eq v v0); Intros.
Rewrite (H1 I); Simpl.
Rewrite (ics_aux_ok (interp_m (Aplus Aone Aone) v0)
                 (canonical_sum_merge c c0));
Rewrite (ics_aux_ok (interp_vl v0) c);
Rewrite (ics_aux_ok (interp_vl v0) c0); Rewrite (
H c0).
Rewrite (interp_m_ok (Aplus Aone Aone) v0).
Setoid_replace (Amult (Aplus Aone Aone) (interp_vl v0))
 with (Aplus (Amult Aone (interp_vl v0)) (Amult Aone (interp_vl v0)));
Setoid_replace (Aplus
                 (Aplus (Amult Aone (interp_vl v0))
                   (Amult Aone (interp_vl v0)))
                 (Aplus (interp_setcs c) (interp_setcs c0)))
 with (Aplus (Amult Aone (interp_vl v0))
        (Aplus (Amult Aone (interp_vl v0))
          (Aplus (interp_setcs c) (interp_setcs c0))));
Setoid_replace (Aplus (Aplus (interp_vl v0) (interp_setcs c))
                 (Aplus (interp_vl v0) (interp_setcs c0)))
 with (Aplus (interp_vl v0)
        (Aplus (interp_setcs c) (Aplus (interp_vl v0) (interp_setcs c0)))).
Setoid_replace (Amult Aone (interp_vl v0)) with (interp_vl v0); Auto.

Elim (varlist_lt v v0); Simpl.
Rewrite (ics_aux_ok (interp_vl v)
                 (canonical_sum_merge c (Cons_varlist v0 c0)));
Rewrite (ics_aux_ok (interp_vl v) c);
Rewrite (ics_aux_ok (interp_vl v0) c0);
Rewrite (H (Cons_varlist v0 c0)); Simpl.
Rewrite (ics_aux_ok (interp_vl v0) c0); Auto.

Rewrite (ics_aux_ok (interp_vl v0)
                 (Fix csm_aux2
                    {csm_aux2 [s2:canonical_sum] : canonical_sum :=
                       Cases (s2) of
                         Nil_monom => (Cons_varlist v c)
                       | (Cons_monom c2 l2 t2) => 
                          (if (varlist_eq v l2)
                           then
                            (Cons_monom (Aplus Aone c2) v
                              (canonical_sum_merge c t2))
                           else
                            (if (varlist_lt v l2)
                             then
                              (Cons_varlist v
                                (canonical_sum_merge c s2))
                             else (Cons_monom c2 l2 (csm_aux2 t2))))
                       | (Cons_varlist l2 t2) => 
                          (if (varlist_eq v l2)
                           then
                            (Cons_monom (Aplus Aone Aone) v
                              (canonical_sum_merge c t2))
                           else
                            (if (varlist_lt v l2)
                             then
                              (Cons_varlist v
                                (canonical_sum_merge c s2))
                             else (Cons_varlist l2 (csm_aux2 t2))))
                       end} c0)); Rewrite H0.
Rewrite (ics_aux_ok (interp_vl v) c);
Rewrite (ics_aux_ok (interp_vl v0) c0); Simpl; Auto.
Save.

Lemma monom_insert_ok: (a:A)(l:varlist)(s:canonical_sum)
 (Aequiv (interp_setcs (monom_insert a l s)) 
   (Aplus (Amult a (interp_vl l)) (interp_setcs s))).
Proof.
Induction s; Intros.
Simpl; Rewrite (interp_m_ok a l); Trivial.

Simpl; Generalize (varlist_eq_prop l v); Elim (varlist_eq l v).
Intro Hr; Rewrite (Hr I); Simpl.
Rewrite (ics_aux_ok (interp_m (Aplus a a0) v) c);
Rewrite (ics_aux_ok (interp_m a0 v) c).
Rewrite (interp_m_ok (Aplus a a0) v);
Rewrite (interp_m_ok a0 v).
Setoid_replace (Amult (Aplus a a0) (interp_vl v))
 with (Aplus (Amult a (interp_vl v)) (Amult a0 (interp_vl v))).
Auto.

Elim (varlist_lt l v); Simpl; Intros.
Rewrite (ics_aux_ok (interp_m a0 v) c).
Rewrite (interp_m_ok a0 v); Rewrite (interp_m_ok a l).
Auto.

Rewrite (ics_aux_ok (interp_m a0 v) (monom_insert a l c));
Rewrite (ics_aux_ok (interp_m a0 v) c); Rewrite H.
Auto.

Simpl.
Generalize (varlist_eq_prop l v); Elim (varlist_eq l v).
Intro Hr; Rewrite (Hr I); Simpl.
Rewrite (ics_aux_ok (interp_m (Aplus a Aone) v) c);
Rewrite (ics_aux_ok (interp_vl v) c).
Rewrite (interp_m_ok (Aplus a Aone) v).
Setoid_replace (Amult (Aplus a Aone) (interp_vl v))
 with (Aplus (Amult a (interp_vl v)) (Amult Aone (interp_vl v))).
Setoid_replace (Amult Aone (interp_vl v)) with (interp_vl v).
Auto.

Elim (varlist_lt l v); Simpl; Intros; Auto.
Rewrite (ics_aux_ok (interp_vl v) (monom_insert a l c));
Rewrite H.
Rewrite (ics_aux_ok (interp_vl v) c); Auto.
Save.

Lemma varlist_insert_ok :
 (l:varlist)(s:canonical_sum)
 (Aequiv (interp_setcs (varlist_insert l s)) 
   (Aplus (interp_vl l) (interp_setcs s))).
Proof.
Induction s; Simpl; Intros.
Trivial.

Generalize (varlist_eq_prop l v); Elim (varlist_eq l v).
Intro Hr; Rewrite (Hr I); Simpl.
Rewrite (ics_aux_ok (interp_m (Aplus Aone a) v) c);
Rewrite (ics_aux_ok (interp_m a v) c).
Rewrite (interp_m_ok (Aplus Aone a) v);
Rewrite (interp_m_ok a v).
Setoid_replace (Amult (Aplus Aone a) (interp_vl v))
 with (Aplus (Amult Aone (interp_vl v)) (Amult a (interp_vl v))).
Setoid_replace (Amult Aone (interp_vl v)) with (interp_vl v); Auto.

Elim (varlist_lt l v); Simpl; Intros; Auto.
Rewrite (ics_aux_ok (interp_m a v) (varlist_insert l c));
Rewrite (ics_aux_ok (interp_m a v) c).
Rewrite (interp_m_ok a v).
Rewrite H; Auto.

Generalize (varlist_eq_prop l v); Elim (varlist_eq l v).
Intro Hr; Rewrite (Hr I); Simpl.
Rewrite (ics_aux_ok (interp_m (Aplus Aone Aone) v) c);
Rewrite (ics_aux_ok (interp_vl v) c).
Rewrite (interp_m_ok (Aplus Aone Aone) v).
Setoid_replace (Amult (Aplus Aone Aone) (interp_vl v))
 with (Aplus (Amult Aone (interp_vl v)) (Amult Aone (interp_vl v))).
Setoid_replace (Amult Aone (interp_vl v)) with (interp_vl v); Auto.

Elim (varlist_lt l v); Simpl; Intros; Auto.
Rewrite (ics_aux_ok (interp_vl v) (varlist_insert l c)).
Rewrite H.
Rewrite (ics_aux_ok (interp_vl v) c); Auto.
Save.

Lemma canonical_sum_scalar_ok : (a:A)(s:canonical_sum)
  (Aequiv (interp_setcs (canonical_sum_scalar a s)) (Amult a (interp_setcs s))).
Proof.
Induction s; Simpl; Intros.
Trivial.

Rewrite (ics_aux_ok (interp_m (Amult a a0) v)
                 (canonical_sum_scalar a c));
Rewrite (ics_aux_ok (interp_m a0 v) c).
Rewrite (interp_m_ok (Amult a a0) v);
Rewrite (interp_m_ok a0 v).
Rewrite H.
Setoid_replace (Amult a (Aplus (Amult a0 (interp_vl v)) (interp_setcs c)))
 with (Aplus (Amult a (Amult a0 (interp_vl v))) (Amult a (interp_setcs c))).
Auto.

Rewrite (ics_aux_ok (interp_m a v) (canonical_sum_scalar a c));
Rewrite (ics_aux_ok (interp_vl v) c); Rewrite H.
Rewrite (interp_m_ok a v).
Auto.
Save.

Lemma canonical_sum_scalar2_ok : (l:varlist; s:canonical_sum)
  (Aequiv (interp_setcs (canonical_sum_scalar2 l s)) (Amult (interp_vl l) (interp_setcs s))).
Proof.
Induction s; Simpl; Intros; Auto.
Rewrite (monom_insert_ok a (varlist_merge l v)
                 (canonical_sum_scalar2 l c)).
Rewrite (ics_aux_ok (interp_m a v) c).
Rewrite (interp_m_ok a v).
Rewrite H.
Rewrite (varlist_merge_ok l v).
Setoid_replace (Amult (interp_vl l)
                 (Aplus (Amult a (interp_vl v)) (interp_setcs c)))
 with (Aplus (Amult (interp_vl l) (Amult a (interp_vl v)))
        (Amult (interp_vl l) (interp_setcs c))).
Auto.

Rewrite (varlist_insert_ok (varlist_merge l v)
                 (canonical_sum_scalar2 l c)).
Rewrite (ics_aux_ok (interp_vl v) c).
Rewrite H.
Rewrite (varlist_merge_ok l v).
Auto.
Save.

Lemma canonical_sum_scalar3_ok : (c:A; l:varlist; s:canonical_sum)
  (Aequiv (interp_setcs (canonical_sum_scalar3 c l s)) (Amult c (Amult (interp_vl l) (interp_setcs s)))).
Proof.
Induction s; Simpl; Intros.
Rewrite (SSR_mult_zero_right S T (interp_vl l)).
Auto.

Rewrite (monom_insert_ok (Amult c a) (varlist_merge l v)
                 (canonical_sum_scalar3 c l c0)).
Rewrite (ics_aux_ok (interp_m a v) c0).
Rewrite (interp_m_ok a v).
Rewrite H.
Rewrite (varlist_merge_ok l v).
Setoid_replace (Amult (interp_vl l)
                 (Aplus (Amult a (interp_vl v)) (interp_setcs c0)))
 with (Aplus (Amult (interp_vl l) (Amult a (interp_vl v)))
        (Amult (interp_vl l) (interp_setcs c0))).
Setoid_replace (Amult c
                 (Aplus (Amult (interp_vl l) (Amult a (interp_vl v)))
                   (Amult (interp_vl l) (interp_setcs c0))))
 with (Aplus (Amult c (Amult (interp_vl l) (Amult a (interp_vl v))))
        (Amult c (Amult (interp_vl l) (interp_setcs c0)))).
Setoid_replace (Amult (Amult c a) (Amult (interp_vl l) (interp_vl v)))
 with (Amult c (Amult a (Amult (interp_vl l) (interp_vl v)))).
Auto.

Rewrite (monom_insert_ok c (varlist_merge l v)
                 (canonical_sum_scalar3 c l c0)).
Rewrite (ics_aux_ok (interp_vl v) c0).
Rewrite H.
Rewrite (varlist_merge_ok l v).
Setoid_replace (Aplus (Amult c (Amult (interp_vl l) (interp_vl v)))
                 (Amult c (Amult (interp_vl l) (interp_setcs c0))))
 with (Amult c
        (Aplus (Amult (interp_vl l) (interp_vl v))
          (Amult (interp_vl l) (interp_setcs c0)))).
Auto.
Save.

Lemma canonical_sum_prod_ok : (x,y:canonical_sum)
  (Aequiv (interp_setcs (canonical_sum_prod x y)) (Amult (interp_setcs x) (interp_setcs y))).
Proof.
Induction x; Simpl; Intros.
Trivial.

Rewrite (canonical_sum_merge_ok (canonical_sum_scalar3 a v y)
                 (canonical_sum_prod c y)).
Rewrite (canonical_sum_scalar3_ok a v y).
Rewrite (ics_aux_ok (interp_m a v) c).
Rewrite (interp_m_ok a v).
Rewrite (H y).
Setoid_replace (Amult a (Amult (interp_vl v) (interp_setcs y)))
 with (Amult (Amult a (interp_vl v)) (interp_setcs y)).
Setoid_replace (Amult (Aplus (Amult a (interp_vl v)) (interp_setcs c))
                 (interp_setcs y))
 with (Aplus (Amult (Amult a (interp_vl v)) (interp_setcs y))
        (Amult (interp_setcs c) (interp_setcs y))).
Trivial.

Rewrite (canonical_sum_merge_ok (canonical_sum_scalar2 v y)
                 (canonical_sum_prod c y)).
Rewrite (canonical_sum_scalar2_ok v y).
Rewrite (ics_aux_ok (interp_vl v) c).
Rewrite (H y).
Trivial.
Save.

Theorem setspolynomial_normalize_ok : (p:setspolynomial)
  (Aequiv (interp_setcs (setspolynomial_normalize p)) (interp_setsp p)).
Proof.
Induction p; Simpl; Intros; Trivial.
Rewrite (canonical_sum_merge_ok (setspolynomial_normalize s)
                 (setspolynomial_normalize s0)).
Rewrite H; Rewrite H0; Trivial.

Rewrite (canonical_sum_prod_ok (setspolynomial_normalize s)
                 (setspolynomial_normalize s0)).
Rewrite H; Rewrite H0; Trivial.
Save.

Lemma canonical_sum_simplify_ok : (s:canonical_sum)
  (Aequiv (interp_setcs (canonical_sum_simplify s)) (interp_setcs s)).
Proof.
Induction s; Simpl; Intros.
Trivial.

Generalize (SSR_eq_prop T 9!a 10!Azero).
Elim (Aeq a Azero).
Simpl.
Intros.
Rewrite (ics_aux_ok (interp_m a v) c).
Rewrite (interp_m_ok a v).
Rewrite (H0 I).
Setoid_replace (Amult Azero (interp_vl v)) with Azero.
Rewrite H.
Trivial.

Intros; Simpl.
Generalize (SSR_eq_prop T 9!a 10!Aone).
Elim (Aeq a Aone).
Intros.
Rewrite (ics_aux_ok (interp_m a v) c).
Rewrite (interp_m_ok a v).
Rewrite (H1 I).
Simpl.
Rewrite (ics_aux_ok (interp_vl v) (canonical_sum_simplify c)).
Rewrite H.
Auto.

Simpl.
Intros.
Rewrite (ics_aux_ok (interp_m a v) (canonical_sum_simplify c)).
Rewrite (ics_aux_ok (interp_m a v) c).
Rewrite H; Trivial.

Rewrite (ics_aux_ok (interp_vl v) (canonical_sum_simplify c)).
Rewrite H.
Auto.
Save.

Theorem setspolynomial_simplify_ok : (p:setspolynomial)
  (Aequiv (interp_setcs (setspolynomial_simplify p)) (interp_setsp p)).
Proof.
Intro.
Unfold setspolynomial_simplify.
Rewrite (canonical_sum_simplify_ok (setspolynomial_normalize p)).
Exact (setspolynomial_normalize_ok p).
Save.

End semi_setoid_rings.

Implicits Cons_varlist.
Implicits Cons_monom.
Implicits SetSPconst.
Implicits SetSPplus.
Implicits SetSPmult.



Section setoid_rings.

Set Implicit Arguments.

Variable vm : (varmap A).
Variable T : (Setoid_Ring_Theory Aequiv Aplus Amult Aone Azero Aopp Aeq).

Hint STh_plus_sym_T := Resolve (STh_plus_sym T).
Hint STh_plus_assoc_T := Resolve (STh_plus_assoc T).
Hint STh_plus_assoc2_T := Resolve (STh_plus_assoc2 S T).
Hint STh_mult_sym_T := Resolve (STh_mult_sym T).
Hint STh_mult_assoc_T := Resolve (STh_mult_assoc T).
Hint STh_mult_assoc2_T := Resolve (STh_mult_assoc2 S T).
Hint STh_plus_zero_left_T := Resolve (STh_plus_zero_left T).
Hint STh_plus_zero_left2_T := Resolve (STh_plus_zero_left2 S T).
Hint STh_mult_one_left_T := Resolve (STh_mult_one_left T).
Hint STh_mult_one_left2_T := Resolve (STh_mult_one_left2 S T).
Hint STh_mult_zero_left_T := Resolve (STh_mult_zero_left S plus_morph mult_morph T).
Hint STh_mult_zero_left2_T := Resolve (STh_mult_zero_left2 S plus_morph mult_morph T).
Hint STh_distr_left_T := Resolve (STh_distr_left T).
Hint STh_distr_left2_T := Resolve (STh_distr_left2 S T).
Hint STh_plus_reg_left_T := Resolve (STh_plus_reg_left S plus_morph T).
Hint STh_plus_permute_T := Resolve (STh_plus_permute S plus_morph T).
Hint STh_mult_permute_T := Resolve (STh_mult_permute S mult_morph T).
Hint STh_distr_right_T := Resolve (STh_distr_right S plus_morph T).
Hint STh_distr_right2_T := Resolve (STh_distr_right2 S plus_morph T).
Hint STh_mult_zero_right_T := Resolve (STh_mult_zero_right S plus_morph mult_morph T).
Hint STh_mult_zero_right2_T := Resolve (STh_mult_zero_right2 S plus_morph mult_morph T).
Hint STh_plus_zero_right_T := Resolve (STh_plus_zero_right S T).
Hint STh_plus_zero_right2_T := Resolve (STh_plus_zero_right2 S T).
Hint STh_mult_one_right_T := Resolve (STh_mult_one_right S T).
Hint STh_mult_one_right2_T := Resolve (STh_mult_one_right2 S T).
Hint STh_plus_reg_right_T := Resolve (STh_plus_reg_right S plus_morph T).
Hints Resolve refl_equal sym_equal trans_equal.
(*Hints Resolve refl_eqT sym_eqT trans_eqT.*)
Hints Immediate T.


(*** Definitions *)

Inductive Type setpolynomial := 
  SetPvar : index -> setpolynomial
| SetPconst : A -> setpolynomial
| SetPplus : setpolynomial -> setpolynomial -> setpolynomial
| SetPmult : setpolynomial -> setpolynomial -> setpolynomial
| SetPopp : setpolynomial -> setpolynomial.

Fixpoint setpolynomial_normalize [x:setpolynomial] : canonical_sum :=
 Cases x of
 | (SetPplus l r) => (canonical_sum_merge
     (setpolynomial_normalize l) 
     (setpolynomial_normalize r))
 | (SetPmult l r) => (canonical_sum_prod
     (setpolynomial_normalize l)
     (setpolynomial_normalize r))
 | (SetPconst c)  => (Cons_monom c Nil_var Nil_monom)
 | (SetPvar i)    => (Cons_varlist (Cons_var i Nil_var) Nil_monom)
 | (SetPopp p)    => (canonical_sum_scalar3
     (Aopp Aone) Nil_var
     (setpolynomial_normalize p))
 end.

Definition setpolynomial_simplify :=
 [x:setpolynomial](canonical_sum_simplify (setpolynomial_normalize x)).

Fixpoint setspolynomial_of [x:setpolynomial] : setspolynomial :=
 Cases x of 
 | (SetPplus l r) => (SetSPplus (setspolynomial_of l) (setspolynomial_of r))
 | (SetPmult l r) => (SetSPmult (setspolynomial_of l) (setspolynomial_of r))
 | (SetPconst c)  => (SetSPconst c)
 | (SetPvar i)    => (SetSPvar i)
 | (SetPopp p)    => (SetSPmult (SetSPconst (Aopp Aone)) (setspolynomial_of p))
 end.

(*** Interpretation *)

Fixpoint interp_setp [p:setpolynomial] : A :=
 Cases p of
 | (SetPconst c)    => c
 | (SetPvar i)      => (varmap_find Azero i vm)
 | (SetPplus p1 p2) => (Aplus (interp_setp p1) (interp_setp p2))
 | (SetPmult p1 p2) => (Amult (interp_setp p1) (interp_setp p2))
 | (SetPopp p1)     => (Aopp (interp_setp p1))
 end.

(*** Properties *)

Unset Implicit Arguments.

Lemma setspolynomial_of_ok : (p:setpolynomial)
 (Aequiv (interp_setp p) (interp_setsp vm (setspolynomial_of p))).
Induction p; Trivial; Simpl; Intros.
Rewrite H; Rewrite H0; Trivial.
Rewrite H; Rewrite H0; Trivial.
Rewrite H.
Rewrite (STh_opp_mult_left2 S plus_morph mult_morph T Aone
                 (interp_setsp vm (setspolynomial_of s))).
Rewrite (STh_mult_one_left T
                 (interp_setsp vm (setspolynomial_of s))).
Trivial.
Save.

Theorem setpolynomial_normalize_ok : (p:setpolynomial)
 (setpolynomial_normalize p)
  ==(setspolynomial_normalize (setspolynomial_of p)).
Induction p; Trivial; Simpl; Intros.
Rewrite H; Rewrite H0; Reflexivity.
Rewrite H; Rewrite H0; Reflexivity.
Rewrite H; Simpl.
Elim (canonical_sum_scalar3 (Aopp Aone) Nil_var
   (setspolynomial_normalize (setspolynomial_of s)));
 [ Reflexivity
 | Simpl; Intros; Rewrite H0; Reflexivity
 | Simpl; Intros; Rewrite H0; Reflexivity ].
Save.

Theorem setpolynomial_simplify_ok : (p:setpolynomial)
 (Aequiv (interp_setcs vm (setpolynomial_simplify p)) (interp_setp p)).
Intro.
Unfold setpolynomial_simplify.
Rewrite (setspolynomial_of_ok p).
Rewrite setpolynomial_normalize_ok.
Rewrite (canonical_sum_simplify_ok vm
   (Semi_Setoid_Ring_Theory_of A Aequiv S Aplus Amult Aone Azero Aopp
    Aeq plus_morph mult_morph T)
   (setspolynomial_normalize (setspolynomial_of p))).
Rewrite (setspolynomial_normalize_ok vm 
   (Semi_Setoid_Ring_Theory_of A Aequiv S Aplus Amult Aone Azero Aopp
    Aeq plus_morph mult_morph T) (setspolynomial_of p)).
Trivial.
Save.

End setoid_rings.

End setoid.
