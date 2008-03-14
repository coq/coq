Require Export Setoid.
Set Implicit Arguments.
Section feq.
Variables A B:Type.
Definition feq (f g: A -> B):=forall a, (f a)=(g a).
Infix "=f":= feq  (at level 80, right associativity).
Hint Unfold feq.

Lemma feq_refl: forall f, f =f f.
intuition.
Qed.
                                                                                
Lemma feq_sym: forall f g, f =f g-> g =f f.
intuition.
Qed.
                                                                                
Lemma feq_trans: forall f g h, f =f g-> g =f h -> f  =f h.
unfold feq. intuition.
rewrite H.
auto.
Qed.
End feq.
Infix "=f":= feq  (at level 80, right associativity).
Hint Unfold feq. Hint Resolve feq_refl feq_sym feq_trans.
                                                                                
Variable K:(nat -> nat)->Prop.
Variable K_ext:forall a b, (K a)->(a =f b)->(K b).

Add Relation (fun A B:Type => A -> B) feq
 reflexivity proved by feq_refl
 symmetry proved by feq_sym
 transitivity proved by feq_trans as funsetoid.
                                                                             
Add Morphism K with signature feq ==> iff as K_ext1.
intuition. apply (K_ext H0 H).
intuition. assert (x2 =f x1);auto.  apply (K_ext H0 H1).
Qed.

Lemma three:forall n, forall a, (K a)->(a =f (fun m => (a (n+m))))-> (K (fun m
=> (a (n+m)))).
intuition.
setoid_rewrite <- H0.
assumption.
Qed.

