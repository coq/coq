
(* $Id$ *)

Section Dependent_Equality.

Variable U : Set.
Variable P : U->Set.

Inductive eq_dep [p:U;x:(P p)] : (q:U)(P q)->Prop :=
   eq_dep_intro : (eq_dep p x p x).
Hint constr_eq_dep : core v62 := Constructors eq_dep.

Lemma  eq_dep_sym : (p,q:U)(x:(P p))(y:(P q))(eq_dep p x q y)->(eq_dep q y p x).
Proof.
Induction 1; Auto.
Qed.
Hints Immediate eq_dep_sym : core v62.

Lemma eq_dep_trans : (p,q,r:U)(x:(P p))(y:(P q))(z:(P r))
     (eq_dep p x q y)->(eq_dep q y r z)->(eq_dep p x r z).
Proof.
Induction 1; Auto.
Qed.

Inductive eq_dep1 [p:U;x:(P p);q:U;y:(P q)] : Prop :=
   eq_dep1_intro : (h:q=p)
                  (x=(eq_rec U q P y p h))->(eq_dep1 p x q y).

Axiom eq_rec_eq : (p:U)(Q:U->Set)(x:(Q p))(h:p=p)
                  x=(eq_rec U p Q x p h).


Lemma eq_dep1_dep :
      (p:U)(x:(P p))(q:U)(y:(P q))(eq_dep1 p x q y)->(eq_dep p x q y).
Proof.
Induction 1; Intros eq_qp.
Cut (h:q=p)(y0:(P q))
    (x=(eq_rec U q P y0 p h))->(eq_dep p x q y0).
Intros; Apply H0 with eq_qp; Auto.
Rewrite eq_qp; Intros h y0.
Elim eq_rec_eq.
Induction 1; Auto.
Qed.

Lemma eq_dep_dep1 : (p,q:U)(x:(P p))(y:(P q))(eq_dep p x q y)->(eq_dep1 p x q y).
Proof.
Induction 1; Intros.
Apply eq_dep1_intro with (refl_equal U p).
Simpl; Trivial.
Qed.

Lemma eq_dep1_eq : (p:U)(x,y:(P p))(eq_dep1 p x p y)->x=y.
Proof.
Induction 1; Intro.
Elim eq_rec_eq; Auto.
Qed.

Lemma eq_dep_eq : (p:U)(x,y:(P p))(eq_dep p x p y)->x=y.
Proof.
Intros; Apply eq_dep1_eq; Apply eq_dep_dep1; Trivial.
Qed.

Lemma equiv_eqex_eqdep : (p,q:U)(x:(P p))(y:(P q)) 
    (existS U P p x)=(existS U P q y) <-> (eq_dep p x q y).
Proof.
Split. 
Intros.
Generalize (eq_ind (sigS U P) (existS U P q y)
      [pr:(sigS U P)] (eq_dep  (projS1 U P pr) (projS2 U P pr) q y)) .
Proof.
Simpl.
Intro.
Generalize (H0 (eq_dep_intro q y)) .
Intro.
Apply (H1 (existS U P p x)).
Auto.
Intros.
Elim H.
Auto.
Qed.


Lemma inj_pair2: (p:U)(x,y:(P p))
    (existS U P p x)=(existS U P p y)-> x=y.
Proof.
Intros.
Apply eq_dep_eq.
Generalize (equiv_eqex_eqdep p p x y) .
Induction 1.
Intros.
Auto.
Qed.

End Dependent_Equality.

Hints Resolve eq_dep_intro : core v62.
Hints Immediate eq_dep_sym eq_dep_eq : core v62.
