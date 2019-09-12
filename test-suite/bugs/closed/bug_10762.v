
Set Implicit Arguments.

Generalizable Variables A B.
Parameter val: Type.

Class Enc (A:Type) : Type :=
  make_Enc { enc : A -> val }.

Hint Mode Enc + : typeclass_instances.

Parameter bar : forall A (EA:Enc A), EA = EA.

Parameter foo : forall (P:Prop),
   P ->
   P = P ->
   True.

Parameter id : forall (P:Prop),
  P -> P.

  Check enc.

  Lemma test : True.
  eapply foo; [ eapply bar | apply id]. apply id.
  (* eapply bar introduces an unresolved typeclass evar that is no longer
     a candidate after the application (eapply should leave typeclass goals shelved).
     We ensure that this happens also _across_ goals in `[ | ]` and not only at `.`..
      *)
  Abort.
