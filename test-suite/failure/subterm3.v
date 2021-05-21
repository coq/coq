(* An example showing that prop-extensionality is incompatible with
   powerful extensions of the guard condition.
   This is a variation on the example in subterm2, exploiting
   missing typing constraints in the commutative cut subterm rule
   (subterm2 is using the same flaw but for the match rule).

   Example due to Cristóbal Camarero on Coq-Club.
 *)

Axiom prop_ext: forall P Q, (P <-> Q) -> P=Q.

Inductive True2 : Prop := I3 : (False -> True2) -> True2.

Theorem T3T: True2 = True.
Proof.
apply prop_ext; split; auto.
intros; constructor; apply False_rect.
Qed.

Theorem T3F_FT3F : (True2 -> False) = ((False -> True2) -> False).
Proof.
rewrite T3T.
apply prop_ext; split; auto.
Qed.

Fail Fixpoint loop (x : True2) : False :=
match x with
I3 f => (match T3F_FT3F in _=T return T with eq_refl=> loop end) f
end.

(* Variant *)

Inductive I: Prop := C: (False -> I) -> I.

Lemma I_eq_True: I = True.
Proof.
  apply prop_ext. split.
  - trivial.
  - intros. constructor. apply False_rect.
Defined.

Lemma I_eq_False_impl_I: I = (False -> I).
Proof.
  apply prop_ext. split.
  - trivial.
  - exact C.
Defined.

Inductive eq': Prop -> Prop := eq_refl': eq' I.

Lemma I_eq_False_impl_I': eq' (False -> I).
Proof.
  rewrite <- I_eq_False_impl_I. constructor.
Defined.

Fail Fixpoint loop x :=
  match x with
    C f =>
    match I_eq_False_impl_I' in eq' T return T -> False with
      eq_refl' => fun x => loop x
    end f
  end.
