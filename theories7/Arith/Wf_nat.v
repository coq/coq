(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Well-founded relations and natural numbers *)

Require Lt.

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n,p:nat.

Chapter  Well_founded_Nat.

Variable A : Set.

Variable f : A -> nat.
Definition ltof := [a,b:A](lt (f a) (f b)).
Definition gtof := [a,b:A](gt (f b) (f a)).

Theorem well_founded_ltof : (well_founded A ltof).
Proof.
Red.
Cut (n:nat)(a:A)(lt (f a) n)->(Acc A ltof a).
Intros H a;  Apply (H (S (f a))); Auto with arith.
NewInduction n.
Intros; Absurd (lt (f a) O); Auto with arith.
Intros a ltSma.
Apply Acc_intro.
Unfold ltof; Intros b ltfafb.
Apply IHn.
Apply lt_le_trans with (f a); Auto with arith.
Qed.

Theorem  well_founded_gtof : (well_founded A gtof).
Proof well_founded_ltof.

(** It is possible to directly prove the induction principle going
   back to primitive recursion on natural numbers ([induction_ltof1])
   or to use the previous lemmas to extract a program with a fixpoint
   ([induction_ltof2]) 

the ML-like program for [induction_ltof1] is : [[
   let induction_ltof1 F a = indrec ((f a)+1) a 
   where rec indrec = 
        function 0    -> (function a -> error)
               |(S m) -> (function a -> (F a (function y -> indrec y m)));;
]]

the ML-like program for [induction_ltof2] is : [[
   let induction_ltof2 F a = indrec a
   where rec indrec a = F a indrec;;
]] *)

Theorem induction_ltof1 
  : (P:A->Set)((x:A)((y:A)(ltof y x)->(P y))->(P x))->(a:A)(P a).
Proof.
Intros P F; Cut (n:nat)(a:A)(lt (f a) n)->(P a).
Intros H a;  Apply (H (S (f a))); Auto with arith.
NewInduction n.
Intros; Absurd (lt (f a) O); Auto with arith.
Intros a ltSma.
Apply F.
Unfold ltof; Intros b ltfafb.
Apply IHn.
Apply lt_le_trans with (f a); Auto with arith.
Defined. 

Theorem induction_gtof1 
  : (P:A->Set)((x:A)((y:A)(gtof y x)->(P y))->(P x))->(a:A)(P a).
Proof.
Exact induction_ltof1.
Defined.

Theorem induction_ltof2 
  : (P:A->Set)((x:A)((y:A)(ltof y x)->(P y))->(P x))->(a:A)(P a).
Proof.
Exact (well_founded_induction A ltof well_founded_ltof).
Defined.

Theorem induction_gtof2 
  : (P:A->Set)((x:A)((y:A)(gtof y x)->(P y))->(P x))->(a:A)(P a).
Proof.
Exact induction_ltof2.
Defined.

(** If a relation [R] is compatible with [lt] i.e. if [x R y => f(x) < f(y)]
    then [R] is well-founded. *)

Variable R : A->A->Prop.

Hypothesis H_compat : (x,y:A) (R x y) -> (lt (f x) (f y)).

Theorem well_founded_lt_compat : (well_founded A R).
Proof.
Red.
Cut (n:nat)(a:A)(lt (f a) n)->(Acc A R a).
Intros H a; Apply (H (S (f a))); Auto with arith.
NewInduction n.
Intros; Absurd (lt (f a) O); Auto with arith.
Intros a ltSma.
Apply Acc_intro.
Intros b ltfafb.
Apply IHn.
Apply lt_le_trans with (f a); Auto with arith.
Qed.

End Well_founded_Nat.

Lemma lt_wf : (well_founded nat lt).
Proof (well_founded_ltof nat [m:nat]m).

Lemma lt_wf_rec1 : (p:nat)(P:nat->Set)
              ((n:nat)((m:nat)(lt m n)->(P m))->(P n)) -> (P p).
Proof.
Exact [p:nat][P:nat->Set][F:(n:nat)((m:nat)(lt m n)->(P m))->(P n)]
     (induction_ltof1 nat [m:nat]m P F p).
Defined.

Lemma lt_wf_rec : (p:nat)(P:nat->Set)
              ((n:nat)((m:nat)(lt m n)->(P m))->(P n)) -> (P p).
Proof.
Exact [p:nat][P:nat->Set][F:(n:nat)((m:nat)(lt m n)->(P m))->(P n)]
     (induction_ltof2 nat [m:nat]m P F p).
Defined.

Lemma lt_wf_ind : (p:nat)(P:nat->Prop)
              ((n:nat)((m:nat)(lt m n)->(P m))->(P n)) -> (P p).
Intro p; Intros; Elim (lt_wf p); Auto with arith.
Qed.

Lemma gt_wf_rec : (p:nat)(P:nat->Set)
              ((n:nat)((m:nat)(gt n m)->(P m))->(P n)) -> (P p).
Proof.
Exact lt_wf_rec.
Defined.

Lemma gt_wf_ind : (p:nat)(P:nat->Prop)
              ((n:nat)((m:nat)(gt n m)->(P m))->(P n)) -> (P p).
Proof lt_wf_ind.

Lemma lt_wf_double_rec : 
  (P:nat->nat->Set)
  ((n,m:nat)((p,q:nat)(lt p n)->(P p q))->((p:nat)(lt p m)->(P n p))->(P n m))
   -> (p,q:nat)(P p q).
Intros P Hrec p; Pattern p; Apply lt_wf_rec.
Intros n H q; Pattern q; Apply lt_wf_rec; Auto with arith.
Defined.

Lemma lt_wf_double_ind : 
  (P:nat->nat->Prop)
  ((n,m:nat)((p,q:nat)(lt p n)->(P p q))->((p:nat)(lt p m)->(P n p))->(P n m))
   -> (p,q:nat)(P p q).
Intros P Hrec p; Pattern p; Apply lt_wf_ind.
Intros n H q; Pattern q; Apply lt_wf_ind; Auto with arith.
Qed.

Hints Resolve lt_wf : arith.
Hints Resolve well_founded_lt_compat : arith.

Section LT_WF_REL.
Variable A :Set.
Variable R:A->A->Prop.

(* Relational form of inversion *)
Variable F : A -> nat -> Prop.
Definition inv_lt_rel 
 [x,y]:=(EX n | (F x n) & (m:nat)(F y m)->(lt n m)).

Hypothesis F_compat : (x,y:A) (R x y) -> (inv_lt_rel x y).
Remark acc_lt_rel : 
  (x:A)(EX n | (F x n))->(Acc A R x).
Intros x (n,fxn); Generalize x fxn; Clear x fxn.
Pattern n; Apply lt_wf_ind; Intros.
Constructor; Intros.
Case (F_compat y x); Trivial; Intros.
Apply (H x0); Auto.
Save.

Theorem well_founded_inv_lt_rel_compat : (well_founded A R).
Constructor; Intros.
Case (F_compat y a); Trivial; Intros.
Apply acc_lt_rel; Trivial.
Exists x; Trivial.
Save.


End LT_WF_REL.

Lemma well_founded_inv_rel_inv_lt_rel 
  : (A:Set)(F:A->nat->Prop)(well_founded A (inv_lt_rel A F)).
Intros; Apply (well_founded_inv_lt_rel_compat A (inv_lt_rel A F) F); Trivial.
Save.
