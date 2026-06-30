From Corelib Require Import Setoid Morphisms ssreflect ssrfun.

Set Primitive Projections.

(* Positive: [iff] rules are accepted by ssreflect rewrite without depending on
   how [iff] unfolds. *)
Lemma rewrite_iff_rule (P Q : Prop) : (P <-> Q) -> P -> Q.
Proof. by move=> HPQ HP; rw -HPQ. Qed.

(* Positive: a global homogeneous relation that is not declared as a
   RewriteRelation should still be recognized by ssreflect rewrite. *)
Parameter rel_const : forall A : Type, A -> A -> Prop.
Parameter rel_wrap : forall A : Type, A -> A.
Axiom rel_const_conv : forall A (x : A), rel_const A (rel_wrap A x) x.
Axiom rel_const_proper : forall A,
  Proper (rel_const A ==> eq ==> iff) (rel_const A).
Global Existing Instance rel_const_proper.

Lemma rewrite_constant_relation A (x y : A) :
  rel_const A (rel_wrap A (rel_wrap A x)) y -> rel_const A x y.
Proof.
  move=> H.
  rw (rel_const_conv _ (rel_wrap A x)) in H.
  by rw (rel_const_conv _ x) in H.
Qed.

(* Positive: mimic Iris/OFE-style relations exposed through primitive record
   projections, where the relation head seen by ssreflect is a projection. *)
Record rel_car := RelCar {
  rel_sort :> Type;
  rel_dist : rel_sort -> rel_sort -> Prop;
  rel_dist_proper : Proper (rel_dist ==> eq ==> iff) rel_dist;
}.

Global Instance rel_dist_proper_inst (A : rel_car) :
  Proper (rel_dist A ==> eq ==> iff) (rel_dist A) := rel_dist_proper A.

Parameter rel_compl : forall A : rel_car, A -> A.
Axiom rel_conv : forall (A : rel_car) (x : A), rel_dist A (rel_compl A x) x.

Lemma rewrite_projected_relation (A : rel_car) (x y : A) :
  rel_dist A (rel_compl A (rel_compl A x)) y -> rel_dist A x y.
Proof.
  move=> H.
  rw (rel_conv _ (rel_compl A x)) in H.
  by rw (rel_conv _ x) in H.
Qed.

(* Negative: do not classify function-valued/forall propositions like eqfun as
   homogeneous binary rewrite relations.  A broader fallback used to do that and
   broke Corelib.ssr.ssrfun.v around rewrites such as [-2!eqfg]. *)
Definition local_eqfun {A B} (f g : A -> B) := forall x, f x = g x.
Notation "f =1l g" := (local_eqfun f g) (at level 70).

Lemma eqfun_ssrfun_style A B (f g : B -> A) (x y : B) :
  injective f -> f =1 g -> g x = g y -> x = y.
Proof. by move=> injf eqfg; rw -2!eqfg; apply: injf. Qed.
