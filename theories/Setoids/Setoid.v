(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$: i*)

Require Export Coq.Classes.SetoidTactics.

(** For backward compatibility *)

Definition Setoid_Theory := @Equivalence.
Definition Build_Setoid_Theory := @Build_Equivalence.

Definition Seq_refl A Aeq (s : Setoid_Theory A Aeq) : forall x:A, Aeq x x.
  unfold Setoid_Theory. intros ; reflexivity.
Defined.

Definition Seq_sym A Aeq (s : Setoid_Theory A Aeq) : forall x y:A, Aeq x y -> Aeq y x.
  unfold Setoid_Theory. intros ; symmetry ; assumption.
Defined.

Definition Seq_trans A Aeq (s : Setoid_Theory A Aeq) : forall x y z:A, Aeq x y -> Aeq y z -> Aeq x z.
  unfold Setoid_Theory. intros ; transitivity y ; assumption.
Defined.

(** Some tactics for manipulating Setoid Theory not officially 
    declared as Setoid. *)

Ltac trans_st x := match goal with 
		     | H : Setoid_Theory _ ?eqA |- ?eqA _ _ => 
		       apply (Seq_trans _ _ H) with x; auto
		   end.

Ltac sym_st := match goal with 
		 | H : Setoid_Theory _ ?eqA |- ?eqA _ _ => 
		   apply (Seq_sym _ _ H); auto
	       end.

Ltac refl_st := match goal with 
		  | H : Setoid_Theory _ ?eqA |- ?eqA _ _ => 
		    apply (Seq_refl _ _ H); auto
		end.

Definition gen_st : forall A : Set, Setoid_Theory _ (@eq A).
Proof. 
  constructor; congruence. 
Qed.
  
