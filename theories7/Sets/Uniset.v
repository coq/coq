(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Sets as characteristic functions *)

(* G. Huet 1-9-95 *)
(* Updated Papageno 12/98 *)

Require Bool.

Set Implicit Arguments.

Section defs.

Variable A : Set.
Variable eqA : A -> A -> Prop.
Hypothesis eqA_dec : (x,y:A){(eqA x y)}+{~(eqA x y)}.

Inductive uniset : Set := 
      Charac : (A->bool) -> uniset.

Definition charac : uniset -> A -> bool :=
  [s:uniset][a:A]Case s of [f:A->bool](f a) end.

Definition Emptyset := (Charac [a:A]false).

Definition Fullset  := (Charac [a:A]true).

Definition Singleton := [a:A](Charac [a':A]
              Case (eqA_dec a a') of 
                   [h:(eqA a a')]  true
                   [h: ~(eqA a a')] false end).

Definition In : uniset -> A -> Prop :=
     [s:uniset][a:A](charac s a)=true.
Hints Unfold In.

(** uniset inclusion *)
Definition incl := [s1,s2:uniset]
    (a:A)(leb (charac s1 a) (charac s2 a)).
Hints Unfold incl.

(** uniset equality *)
Definition seq := [s1,s2:uniset]
    (a:A)(charac s1 a) = (charac s2 a).
Hints Unfold seq.

Lemma leb_refl : (b:bool)(leb b b).
Proof.
NewDestruct b; Simpl; Auto.
Qed.
Hints Resolve leb_refl.

Lemma incl_left : (s1,s2:uniset)(seq s1 s2)->(incl s1 s2).
Proof.
Unfold incl; Intros s1 s2 E a; Elim (E a); Auto.
Qed.

Lemma incl_right : (s1,s2:uniset)(seq s1 s2)->(incl s2 s1).
Proof.
Unfold incl; Intros s1 s2 E a; Elim (E a); Auto.
Qed.

Lemma seq_refl : (x:uniset)(seq x x).
Proof.
NewDestruct x; Unfold seq; Auto.
Qed.
Hints Resolve seq_refl.

Lemma seq_trans : (x,y,z:uniset)(seq x y)->(seq y z)->(seq x z).
Proof.
Unfold seq.
NewDestruct x; NewDestruct y; NewDestruct z; Simpl; Intros.
Rewrite H; Auto.
Qed.

Lemma seq_sym : (x,y:uniset)(seq x y)->(seq y x).
Proof.
Unfold seq.
NewDestruct x; NewDestruct y; Simpl; Auto.
Qed.

(** uniset union *)
Definition union := [m1,m2:uniset]
    (Charac [a:A](orb (charac m1 a)(charac m2 a))).

Lemma union_empty_left :
     (x:uniset)(seq x (union Emptyset x)).  
Proof.  
Unfold seq; Unfold union; Simpl; Auto.  
Qed. 
Hints Resolve union_empty_left.

Lemma union_empty_right :
     (x:uniset)(seq x (union x Emptyset)).
Proof.
Unfold seq; Unfold union; Simpl.
Intros x a; Rewrite (orb_b_false (charac x a)); Auto.
Qed.
Hints Resolve union_empty_right.

Lemma union_comm : (x,y:uniset)(seq (union x y) (union y x)).
Proof.
Unfold seq; Unfold charac; Unfold union.
NewDestruct x; NewDestruct y; Auto with bool.
Qed.
Hints Resolve union_comm.

Lemma union_ass : 
      (x,y,z:uniset)(seq (union (union x y) z) (union x (union y z))).
Proof.
Unfold seq; Unfold union; Unfold charac.
NewDestruct x; NewDestruct y; NewDestruct z; Auto with bool.
Qed.
Hints Resolve union_ass.

Lemma seq_left :  (x,y,z:uniset)(seq x y)->(seq (union x z) (union y z)).
Proof.
Unfold seq; Unfold union; Unfold charac.
NewDestruct x; NewDestruct y; NewDestruct z.
Intros; Elim H; Auto.
Qed.
Hints Resolve seq_left.

Lemma seq_right : (x,y,z:uniset)(seq x y)->(seq (union z x) (union z y)).
Proof.
Unfold seq; Unfold union; Unfold charac.
NewDestruct x; NewDestruct y; NewDestruct z.
Intros; Elim H; Auto.
Qed.
Hints Resolve seq_right.


(** All the proofs that follow duplicate [Multiset_of_A] *)

(** Here we should make uniset an abstract datatype, by hiding [Charac],
    [union], [charac]; all further properties are proved abstractly *)

Require Permut.

Lemma union_rotate :
   (x,y,z:uniset)(seq (union x (union y z)) (union z (union x y))).
Proof.
Intros; Apply (op_rotate uniset union seq); Auto.
Exact seq_trans.
Qed.

Lemma seq_congr : (x,y,z,t:uniset)(seq x y)->(seq z t)->
                  (seq (union x z) (union y t)).
Proof.
Intros; Apply (cong_congr uniset union seq); Auto.
Exact seq_trans.
Qed.

Lemma union_perm_left :
   (x,y,z:uniset)(seq (union x (union y z)) (union y (union x z))).
Proof.
Intros; Apply (perm_left uniset union seq); Auto.
Exact seq_trans.
Qed.

Lemma uniset_twist1 : (x,y,z,t:uniset)
   (seq (union x (union (union y z) t)) (union (union y (union x t)) z)).
Proof.
Intros; Apply (twist uniset union seq); Auto.
Exact seq_trans.
Qed.

Lemma uniset_twist2 : (x,y,z,t:uniset)
   (seq (union x (union (union y z) t)) (union (union y (union x z)) t)).
Proof.
Intros; Apply seq_trans with (union (union x (union y z)) t).
Apply seq_sym; Apply union_ass.
Apply seq_left; Apply union_perm_left.
Qed.

(** specific for treesort *)

Lemma treesort_twist1 : (x,y,z,t,u:uniset) (seq u (union y z)) ->
   (seq (union x (union u t)) (union (union y (union x t)) z)).
Proof.
Intros; Apply seq_trans with (union x (union (union y z) t)).
Apply seq_right; Apply seq_left; Trivial.
Apply uniset_twist1.
Qed.

Lemma treesort_twist2 : (x,y,z,t,u:uniset) (seq u (union y z)) ->
   (seq (union x (union u t)) (union (union y (union x z)) t)).
Proof.
Intros; Apply seq_trans with (union x (union (union y z) t)).
Apply seq_right; Apply seq_left; Trivial.
Apply uniset_twist2.
Qed.


(*i theory of minter to do similarly 
Require Min.
(* uniset intersection *)
Definition minter := [m1,m2:uniset]
    (Charac [a:A](andb (charac m1 a)(charac m2 a))).
i*)

End defs.

Unset Implicit Arguments.
