(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file defines dependent equality and shows its equivalence with
    equality on dependent pairs (inhabiting sigma-types). It axiomatizes
    the invariance by substitution of reflexive equality proofs and 
    shows the equivalence between the 4 following statements

    - Invariance by Substitution of Reflexive Equality Proofs.
    - Injectivity of Dependent Equality
    - Uniqueness of Identity Proofs
    - Uniqueness of Reflexive Identity Proofs
    - Streicher's Axiom K

  These statements are independent of the calculus of constructions [2].

  References:

  [1] T. Streicher, Semantical Investigations into Intensional Type Theory,
      Habilitationsschrift, LMU München, 1993.
  [2] M. Hofmann, T. Streicher, The groupoid interpretation of type theory,
      Proceedings of the meeting Twenty-five years of constructive
      type theory, Venice, Oxford University Press, 1998
*)

Section Dependent_Equality.

Variable U : Type.
Variable P : U->Type.

(** Dependent equality *)

Inductive eq_dep [p:U;x:(P p)] : (q:U)(P q)->Prop :=
   eq_dep_intro : (eq_dep p x p x).
Hint constr_eq_dep : core v62 := Constructors eq_dep.

Lemma eq_dep_sym : (p,q:U)(x:(P p))(y:(P q))(eq_dep p x q y)->(eq_dep q y p x).
Proof.
NewDestruct 1; Auto.
Qed.
Hints Immediate eq_dep_sym : core v62.

Lemma eq_dep_trans : (p,q,r:U)(x:(P p))(y:(P q))(z:(P r))
     (eq_dep p x q y)->(eq_dep q y r z)->(eq_dep p x r z).
Proof.
NewDestruct 1; Auto.
Qed.

Inductive eq_dep1 [p:U;x:(P p);q:U;y:(P q)] : Prop :=
   eq_dep1_intro : (h:q=p)
                  (x=(eq_rect U q P y p h))->(eq_dep1 p x q y).

Scheme eq_indd := Induction for eq Sort Prop.

Lemma eq_dep1_dep :
      (p:U)(x:(P p))(q:U)(y:(P q))(eq_dep1 p x q y)->(eq_dep p x q y).
Proof.
NewDestruct 1 as [eq_qp H].
NewDestruct eq_qp using eq_indd.
Rewrite H.
Apply eq_dep_intro.
Qed.

Lemma eq_dep_dep1 : 
  (p,q:U)(x:(P p))(y:(P q))(eq_dep p x q y)->(eq_dep1 p x q y).
Proof.
NewDestruct 1.
Apply eq_dep1_intro with (refl_equal U p).
Simpl; Trivial.
Qed.

(** Invariance by Substitution of Reflexive Equality Proofs *)

Axiom eq_rect_eq : (p:U)(Q:U->Type)(x:(Q p))(h:p=p)
                  x=(eq_rect U p Q x p h).

(** Injectivity of Dependent Equality is a consequence of *)
(** Invariance by Substitution of Reflexive Equality Proof *)

Lemma eq_dep1_eq : (p:U)(x,y:(P p))(eq_dep1 p x p y)->x=y.
Proof.
Destruct 1; Intro.
Rewrite <- eq_rect_eq; Auto.
Qed.

Lemma eq_dep_eq : (p:U)(x,y:(P p))(eq_dep p x p y)->x=y.
Proof.
Intros; Apply eq_dep1_eq; Apply eq_dep_dep1; Trivial.
Qed.

End Dependent_Equality.

(** Uniqueness of Identity Proofs (UIP) is a consequence of *)
(** Injectivity of Dependent Equality *)

Lemma UIP : (U:Type)(x,y:U)(p1,p2:x=y)p1=p2.
Proof.
Intros; Apply eq_dep_eq with P:=[y]x=y.
Elim p2 using eq_indd.
Elim p1 using eq_indd.
Apply eq_dep_intro.
Qed.

(** Uniqueness of Reflexive Identity Proofs is a direct instance of UIP *)

Lemma UIP_refl : (U:Type)(x:U)(p:x=x)p=(refl_equal U x).
Proof.
Intros; Apply UIP.
Qed.

(** Streicher axiom K is a direct consequence of Uniqueness of
    Reflexive Identity Proofs *)

Lemma Streicher_K : (U:Type)(x:U)(P:x=x->Prop)
  (P (refl_equal ? x))->(p:x=x)(P p).
Proof.
Intros; Rewrite UIP_refl; Assumption.
Qed.

(** We finally recover eq_rec_eq (alternatively eq_rect_eq) from K *)

Lemma eq_rec_eq : (U:Type)(P:U->Set)(p:U)(x:(P p))(h:p=p)
  x=(eq_rec U p P x p h).
Proof.
Intros.
Apply Streicher_K with p:=h.
Reflexivity.
Qed.

(** Dependent equality is equivalent to equality on dependent pairs *)

Lemma equiv_eqex_eqdep : (U:Set)(P:U->Set)(p,q:U)(x:(P p))(y:(P q)) 
    (existS U P p x)=(existS U P q y) <-> (eq_dep U P p x q y).
Proof.
Split. 
(* -> *)
Intro H.
Change p with   (projS1 U P (existS U P p x)).
Change 2 x with (projS2 U P (existS U P p x)).
Rewrite H.
Apply eq_dep_intro.
(* <- *)
NewDestruct 1; Reflexivity.
Qed.

(** UIP implies the injectivity of equality on dependent pairs *)

Lemma inj_pair2: (U:Set)(P:U->Set)(p:U)(x,y:(P p))
    (existS U P p x)=(existS U P p y)-> x=y.
Proof.
Intros.
Apply (eq_dep_eq U P).
Generalize (equiv_eqex_eqdep U P p p x y) .
Induction 1.
Intros.
Auto.
Qed.

(** UIP implies the injectivity of equality on dependent pairs *)

Lemma inj_pairT2: (U:Type)(P:U->Type)(p:U)(x,y:(P p))
    (existT U P p x)=(existT U P p y)-> x=y.
Proof.
Intros.
Apply (eq_dep_eq U P).
Change 1 p with (projT1 U P (existT U P p x)).
Change 2 x with (projT2 U P (existT U P p x)).
Rewrite H.
Apply eq_dep_intro.
Qed.

(** The main results to be exported *)

Hints Resolve eq_dep_intro eq_dep_eq : core v62.
Hints Immediate eq_dep_sym : core v62.
Hints Resolve inj_pair2 inj_pairT2 : core.
