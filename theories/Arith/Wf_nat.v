(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Well-founded relations and natural numbers *)

Require Lt.

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
Induction n.
Intros; Absurd (lt (f a) O); Auto with arith.
Intros m Hm a ltSma.
Apply Acc_intro.
Unfold ltof; Intros b ltfafb.
Apply Hm.
Apply lt_le_trans with (f a); Auto with arith.
Qed.

Theorem  well_founded_gtof : (well_founded A gtof).
Proof well_founded_ltof.

(* It is possible to directly prove the induction principle going
   back to primitive recursion on natural numbers ([induction_ltof1])
   or to use the previous lemmas to extract a program with a fixpoint
   ([induction_ltof2]) 
the ML-like program for [induction_ltof1] is :
\begin{verbatim}
   let induction_ltof1 F a = indrec ((f a)+1) a 
   where rec indrec = 
        function 0    -> (function a -> error)
               |(S m) -> (function a -> (F a (function y -> indrec y m)));;
\end{verbatim}
the ML-like program for [induction_ltof2] is :
\begin{verbatim}
   let induction_ltof2 F a = indrec a
   where rec indrec a = F a indrec;;
\end{verbatim}
*)

Theorem induction_ltof1 
  : (P:A->Set)((x:A)((y:A)(ltof y x)->(P y))->(P x))->(a:A)(P a).
Proof.
Intros P F; Cut (n:nat)(a:A)(lt (f a) n)->(P a).
Intros H a;  Apply (H (S (f a))); Auto with arith.
Induction n.
Intros; Absurd (lt (f a) O); Auto with arith.
Intros m Hm a ltSma.
Apply F.
Unfold ltof; Intros b ltfafb.
Apply Hm.
Apply lt_le_trans with (f a); Auto with arith.
Qed. 

Theorem induction_gtof1 
  : (P:A->Set)((x:A)((y:A)(gtof y x)->(P y))->(P x))->(a:A)(P a).
Proof induction_ltof1.

Theorem induction_ltof2 
  : (P:A->Set)((x:A)((y:A)(ltof y x)->(P y))->(P x))->(a:A)(P a).
Proof (well_founded_induction A ltof well_founded_ltof).

Theorem induction_gtof2 
  : (P:A->Set)((x:A)((y:A)(gtof y x)->(P y))->(P x))->(a:A)(P a).
Proof induction_ltof2.


(* If a relation R is compatible with lt i.e. if x R y => f(x) < f(y)
   then R is well-founded. *)

Variable R : A->A->Prop.

Hypothesis H_compat : (x,y:A) (R x y) -> (lt (f x) (f y)).

Theorem well_founded_lt_compat : (well_founded A R).
Proof.
Red.
Cut (n:nat)(a:A)(lt (f a) n)->(Acc A R a).
Intros H a; Apply (H (S (f a))); Auto with arith.
Induction n.
Intros; Absurd (lt (f a) O); Auto with arith.
Intros m Hm a ltSma.
Apply Acc_intro.
Intros b ltfafb.
Apply Hm.
Apply lt_le_trans with (f a); Auto with arith.
Save.

End Well_founded_Nat.

Lemma lt_wf : (well_founded nat lt).
Proof (well_founded_ltof nat [m:nat]m).

Lemma lt_wf_rec1 : (p:nat)(P:nat->Set)
              ((n:nat)((m:nat)(lt m n)->(P m))->(P n)) -> (P p).
Proof [p:nat][P:nat->Set][F:(n:nat)((m:nat)(lt m n)->(P m))->(P n)]
     (induction_ltof1 nat [m:nat]m P F p).

Lemma lt_wf_rec : (p:nat)(P:nat->Set)
              ((n:nat)((m:nat)(lt m n)->(P m))->(P n)) -> (P p).
Proof [p:nat][P:nat->Set][F:(n:nat)((m:nat)(lt m n)->(P m))->(P n)]
     (induction_ltof2 nat [m:nat]m P F p).

Lemma lt_wf_ind : (p:nat)(P:nat->Prop)
              ((n:nat)((m:nat)(lt m n)->(P m))->(P n)) -> (P p).
Intros; Elim (lt_wf p); Auto with arith.
Save.

Lemma gt_wf_rec : (p:nat)(P:nat->Set)
              ((n:nat)((m:nat)(gt n m)->(P m))->(P n)) -> (P p).
Proof lt_wf_rec.

Lemma gt_wf_ind : (p:nat)(P:nat->Prop)
              ((n:nat)((m:nat)(gt n m)->(P m))->(P n)) -> (P p).
Proof lt_wf_ind.

Lemma lt_wf_double_rec : 
  (P:nat->nat->Set)
  ((n,m:nat)((p,q:nat)(lt p n)->(P p q))->((p:nat)(lt p m)->(P n p))->(P n m))
   -> (p,q:nat)(P p q).
Intros P Hrec p; Pattern p; Apply lt_wf_rec.
Intros; Pattern q; Apply lt_wf_rec; Auto with arith.
Save.

Lemma lt_wf_double_ind : 
  (P:nat->nat->Prop)
  ((n,m:nat)((p,q:nat)(lt p n)->(P p q))->((p:nat)(lt p m)->(P n p))->(P n m))
   -> (p,q:nat)(P p q).
Intros P Hrec p; Pattern p; Apply lt_wf_ind.
Intros; Pattern q; Apply lt_wf_ind; Auto with arith.
Save.

Hints Resolve lt_wf : arith.
Hints Resolve well_founded_lt_compat : arith.
