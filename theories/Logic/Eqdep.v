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
Variable P : U -> Type.

(** Dependent equality *)

Inductive eq_dep (p:U) (x:P p) : forall q:U, P q -> Prop :=
    eq_dep_intro : eq_dep p x p x.
Hint Constructors eq_dep: core v62.

Lemma eq_dep_sym :
 forall (p q:U) (x:P p) (y:P q), eq_dep p x q y -> eq_dep q y p x.
Proof.
destruct 1; auto.
Qed.
Hint Immediate eq_dep_sym: core v62.

Lemma eq_dep_trans :
 forall (p q r:U) (x:P p) (y:P q) (z:P r),
   eq_dep p x q y -> eq_dep q y r z -> eq_dep p x r z.
Proof.
destruct 1; auto.
Qed.

Scheme eq_indd := Induction for eq Sort Prop.

Inductive eq_dep1 (p:U) (x:P p) (q:U) (y:P q) : Prop :=
    eq_dep1_intro : forall h:q = p, x = eq_rect q P y p h -> eq_dep1 p x q y.

Lemma eq_dep1_dep :
 forall (p:U) (x:P p) (q:U) (y:P q), eq_dep1 p x q y -> eq_dep p x q y.
Proof.
destruct 1 as (eq_qp, H).
destruct eq_qp using eq_indd.
rewrite H.
apply eq_dep_intro.
Qed.

Lemma eq_dep_dep1 :
 forall (p q:U) (x:P p) (y:P q), eq_dep p x q y -> eq_dep1 p x q y.
Proof.
destruct 1.
apply eq_dep1_intro with (refl_equal p).
simpl in |- *; trivial.
Qed.

(** Invariance by Substitution of Reflexive Equality Proofs *)

Axiom eq_rect_eq :
    forall (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.

(** Injectivity of Dependent Equality is a consequence of *)
(** Invariance by Substitution of Reflexive Equality Proof *)

Lemma eq_dep1_eq : forall (p:U) (x y:P p), eq_dep1 p x p y -> x = y.
Proof.
simple destruct 1; intro.
rewrite <- eq_rect_eq; auto.
Qed.

Lemma eq_dep_eq : forall (p:U) (x y:P p), eq_dep p x p y -> x = y.
Proof.
intros; apply eq_dep1_eq; apply eq_dep_dep1; trivial.
Qed.

End Dependent_Equality.

(** Uniqueness of Identity Proofs (UIP) is a consequence of *)
(** Injectivity of Dependent Equality *)

Lemma UIP : forall (U:Type) (x y:U) (p1 p2:x = y), p1 = p2.
Proof.
intros; apply eq_dep_eq with (P := fun y => x = y).
elim p2 using eq_indd.
elim p1 using eq_indd.
apply eq_dep_intro.
Qed.

(** Uniqueness of Reflexive Identity Proofs is a direct instance of UIP *)

Lemma UIP_refl : forall (U:Type) (x:U) (p:x = x), p = refl_equal x.
Proof.
intros; apply UIP.
Qed.

(** Streicher axiom K is a direct consequence of Uniqueness of
    Reflexive Identity Proofs *)

Lemma Streicher_K :
 forall (U:Type) (x:U) (P:x = x -> Prop),
   P (refl_equal x) -> forall p:x = x, P p.
Proof.
intros; rewrite UIP_refl; assumption.
Qed.

(** We finally recover eq_rec_eq (alternatively eq_rect_eq) from K *)

Lemma eq_rec_eq :
 forall (U:Type) (P:U -> Set) (p:U) (x:P p) (h:p = p), x = eq_rec p P x p h.
Proof.
intros.
apply Streicher_K with (p := h).
reflexivity.
Qed.

(** Dependent equality is equivalent to equality on dependent pairs *)

Lemma equiv_eqex_eqdep :
 forall (U:Set) (P:U -> Set) (p q:U) (x:P p) (y:P q),
   existS P p x = existS P q y <-> eq_dep U P p x q y.
Proof.
split. 
(* -> *)
intro H.
change p with (projS1 (existS P p x)) in |- *.
change x at 2 with (projS2 (existS P p x)) in |- *.
rewrite H.
apply eq_dep_intro.
(* <- *)
destruct 1; reflexivity.
Qed.

(** UIP implies the injectivity of equality on dependent pairs *)

Lemma inj_pair2 :
 forall (U:Set) (P:U -> Set) (p:U) (x y:P p),
   existS P p x = existS P p y -> x = y.
Proof.
intros.
apply (eq_dep_eq U P).
generalize (equiv_eqex_eqdep U P p p x y).
simple induction 1.
intros.
auto.
Qed.

(** UIP implies the injectivity of equality on dependent pairs *)

Lemma inj_pairT2 :
 forall (U:Type) (P:U -> Type) (p:U) (x y:P p),
   existT P p x = existT P p y -> x = y.
Proof.
intros.
apply (eq_dep_eq U P).
change p at 1 with (projT1 (existT P p x)) in |- *.
change x at 2 with (projT2 (existT P p x)) in |- *.
rewrite H.
apply eq_dep_intro.
Qed.

(** The main results to be exported *)

Hint Resolve eq_dep_intro eq_dep_eq: core v62.
Hint Immediate eq_dep_sym: core v62.
Hint Resolve inj_pair2 inj_pairT2: core.
