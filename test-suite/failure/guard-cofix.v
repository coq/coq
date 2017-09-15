(* This script shows, in two different ways, the inconsistency of the
propositional extensionality axiom with the guard condition for cofixpoints. It
is the dual of the problem on fixpoints (cf subterm.v, subterm2.v,
subterm3.v). Posted on Coq-club by Maxime Dénès (02/26/2014). *)

(* First example *)

CoInductive CoFalse : Prop := CF : CoFalse -> False -> CoFalse.

CoInductive Pandora : Prop := C : CoFalse -> Pandora.

Axiom prop_ext : forall P Q : Prop, (P<->Q) -> P = Q.

Lemma foo : Pandora = CoFalse.
apply prop_ext.
constructor.
intro x; destruct x; assumption.
exact C.
Qed.

Fail CoFixpoint loop : CoFalse :=
match foo in (_ = T) return T with eq_refl => C loop end.

Fail Definition ff : False := match loop with CF _ t => t end.

(* Second example *)

Inductive omega : Prop := Omega : omega -> omega.

Lemma H : omega = CoFalse.
Proof.
apply prop_ext; constructor.
  induction 1; assumption.
destruct 1; destruct H0.
Qed.

Fail CoFixpoint loop' : CoFalse :=
  match H in _ = T return T with
    eq_refl =>
    Omega match eq_sym H in _ = T return T with eq_refl => loop' end
  end.

Fail Definition ff' : False := match loop' with CF _ t => t end.
