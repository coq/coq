(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* G. Huet 1-9-95 *)

Require Permut.

Set Implicit Arguments.

Section multiset_defs.

Variable A : Set.
Variable eqA : A -> A -> Prop.
Hypothesis Aeq_dec : (x,y:A){(eqA x y)}+{~(eqA x y)}.

Inductive multiset : Set := 
      Bag : (A->nat) -> multiset.

Definition EmptyBag := (Bag [a:A]O).
Definition SingletonBag := [a:A]
	(Bag [a':A]Cases (Aeq_dec a a') of
                      (left _) => (S O) 
	           | (right _) => O 
                   end
	).

Definition multiplicity : multiset -> A -> nat :=
  [m:multiset][a:A]let (f) = m in (f a).

(** multiset equality *)
Definition meq := [m1,m2:multiset]
    (a:A)(multiplicity m1 a)=(multiplicity m2 a).

Hints Unfold  meq multiplicity.

Lemma meq_refl : (x:multiset)(meq x x).
Proof.
NewDestruct x; Auto.
Qed.
Hints Resolve meq_refl.

Lemma meq_trans : (x,y,z:multiset)(meq x y)->(meq y z)->(meq x z).
Proof.
Unfold meq.
NewDestruct x; NewDestruct y; NewDestruct z.
Intros; Rewrite H; Auto.
Qed.

Lemma meq_sym : (x,y:multiset)(meq x y)->(meq y x).
Proof.
Unfold meq.
NewDestruct x; NewDestruct y; Auto.
Qed.
Hints Immediate meq_sym.

(** multiset union *)
Definition munion := [m1,m2:multiset]
    (Bag [a:A](plus (multiplicity m1 a)(multiplicity m2 a))).

Lemma munion_empty_left :
     (x:multiset)(meq x (munion EmptyBag x)).
Proof.
Unfold meq; Unfold munion; Simpl; Auto.
Qed.
Hints Resolve munion_empty_left.

Lemma munion_empty_right :
     (x:multiset)(meq x (munion x EmptyBag)).
Proof.
Unfold meq; Unfold munion; Simpl; Auto.
Qed.


Require Plus. (* comm. and ass. of plus *)

Lemma munion_comm : (x,y:multiset)(meq (munion x y) (munion y x)).
Proof.
Unfold meq; Unfold multiplicity; Unfold munion.
NewDestruct x; NewDestruct y; Auto with arith.
Qed.
Hints Resolve munion_comm.

Lemma munion_ass : 
      (x,y,z:multiset)(meq (munion (munion x y) z) (munion x (munion y z))).
Proof.
Unfold meq; Unfold munion; Unfold multiplicity.
NewDestruct x; NewDestruct y; NewDestruct z; Auto with arith.
Qed.
Hints Resolve munion_ass.

Lemma meq_left :  (x,y,z:multiset)(meq x y)->(meq (munion x z) (munion y z)).
Proof.
Unfold meq; Unfold munion; Unfold multiplicity.
NewDestruct x; NewDestruct y; NewDestruct z.
Intros; Elim H; Auto with arith.
Qed.
Hints Resolve meq_left.

Lemma meq_right : (x,y,z:multiset)(meq x y)->(meq (munion z x) (munion z y)).
Proof.
Unfold meq; Unfold munion; Unfold multiplicity.
NewDestruct x; NewDestruct y; NewDestruct z.
Intros; Elim H; Auto.
Qed.
Hints Resolve meq_right.


(** Here we should make multiset an abstract datatype, by hiding [Bag],
    [munion], [multiplicity]; all further properties are proved abstractly *)

Lemma munion_rotate :
   (x,y,z:multiset)(meq (munion x (munion y z)) (munion z (munion x y))).
Proof.
Intros; Apply (op_rotate multiset munion meq); Auto.
Exact meq_trans.
Qed.

Lemma meq_congr : (x,y,z,t:multiset)(meq x y)->(meq z t)->
                  (meq (munion x z) (munion y t)).
Proof.
Intros; Apply (cong_congr multiset munion meq); Auto.
Exact meq_trans.
Qed.

Lemma munion_perm_left :
   (x,y,z:multiset)(meq (munion x (munion y z)) (munion y (munion x z))).
Proof.
Intros; Apply (perm_left multiset munion meq); Auto.
Exact meq_trans.
Qed.

Lemma multiset_twist1 : (x,y,z,t:multiset)
   (meq (munion x (munion (munion y z) t)) (munion (munion y (munion x t)) z)).
Proof.
Intros; Apply (twist multiset munion meq); Auto.
Exact meq_trans.
Qed.

Lemma multiset_twist2 : (x,y,z,t:multiset)
   (meq (munion x (munion (munion y z) t)) (munion (munion y (munion x z)) t)).
Proof.
Intros; Apply meq_trans with (munion (munion x (munion y z)) t).
Apply meq_sym; Apply munion_ass.
Apply meq_left; Apply munion_perm_left.
Qed.

(** specific for treesort *)

Lemma treesort_twist1 : (x,y,z,t,u:multiset) (meq u (munion y z)) ->
   (meq (munion x (munion u t)) (munion (munion y (munion x t)) z)).
Proof.
Intros; Apply meq_trans with (munion x (munion (munion y z) t)).
Apply meq_right; Apply meq_left; Trivial.
Apply multiset_twist1.
Qed.

Lemma treesort_twist2 : (x,y,z,t,u:multiset) (meq u (munion y z)) ->
   (meq (munion x (munion u t)) (munion (munion y (munion x z)) t)).
Proof.
Intros; Apply meq_trans with (munion x (munion (munion y z) t)).
Apply meq_right; Apply meq_left; Trivial.
Apply multiset_twist2.
Qed.


(*i theory of minter to do similarly 
Require Min.
(* multiset intersection *)
Definition minter := [m1,m2:multiset]
    (Bag [a:A](min (multiplicity m1 a)(multiplicity m2 a))).
i*)

End multiset_defs.

Unset Implicit Arguments.

Hints Unfold meq multiplicity : v62 datatypes.
Hints Resolve munion_empty_right munion_comm munion_ass meq_left meq_right munion_empty_left : v62 datatypes.
Hints Immediate meq_sym : v62 datatypes.
