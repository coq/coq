(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $id$ *)

Require Export Eqdep_dec.

(* Congruence lemma *)

Theorem Congr_nodep: (A,B:Type)(f,g:A->B)(x,y:A)f==g->x==y->(f x)==(g y).
Intros A B f g x y eq1 eq2;Rewrite eq1;Rewrite eq2;Reflexivity.
Defined.

Theorem Congr_dep:
	(A:Type; P:(A->Type); f,g:((a:A)(P a)); x:A)f==g->(f x)==(g x).
Intros A P f g x e;Rewrite e;Reflexivity.
Defined.

(* Basic application : try to prove that goal is equal to one hypothesis *) 

Lemma convert_goal :  (A,B:Prop)B->(A==B)->A.
Intros A B H E;Rewrite E;Assumption.
Save.

Tactic Definition CCsolve :=
 Match Context With
 [ H: ?1 |- ?2] -> 
        (Assert (?2==?1);[CC|
        Match Reverse Context With 
                [ H: ?1;Heq: (?2==?1)|- ?2] ->(Rewrite Heq;Exact H)]).

