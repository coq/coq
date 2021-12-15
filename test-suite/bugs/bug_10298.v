Set Implicit Arguments.

Generalizable Variables A.

Parameter val : Type.

Class Enc (A:Type) :=
  make_Enc { enc : A -> val }.

Global Instance Enc_dummy : Enc unit.
Admitted.

Definition FORM := forall A (EA:Enc A) (Q:A->Prop), Prop.

Axiom FORM_intro : forall F : FORM, F unit Enc_dummy (fun _ : unit => True).

Definition IDF (F:FORM) : FORM := F.

Parameter ID : forall (G:Prop), G -> G.

Parameter EID : forall A (EA:Enc A) (F:FORM) (Q:A->Prop),
  F _ _ Q ->
  F _ _ Q.

Lemma bla : forall F,
  (forall A (EA:Enc A), IDF F EA (fun (X:A) => True) -> True) ->
  True.
Proof.
  intros F M.
  notypeclasses refine (M _ _ _).
  notypeclasses refine (EID _ _ _ _).
  eapply (ID _).
  Unshelve.
  + apply FORM_intro.
Qed.
