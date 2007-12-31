(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$: i*)

Set Implicit Arguments.

Require Export Setoid_tac.
Require Export Setoid_Prop.

(** For backward compatibility *)

Record Setoid_Theory  (A: Type) (Aeq: relation A) : Prop := 
  { Seq_refl : forall x:A, Aeq x x;
    Seq_sym : forall x y:A, Aeq x y -> Aeq y x;
    Seq_trans : forall x y z:A, Aeq x y -> Aeq y z -> Aeq x z }.

Implicit Arguments Setoid_Theory [].
Implicit Arguments Seq_refl [].
Implicit Arguments Seq_sym [].
Implicit Arguments Seq_trans [].


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
  
