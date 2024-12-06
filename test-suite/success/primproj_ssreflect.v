From Corelib Require Import ssreflect.

Module R.
  #[local] Set Printing Unfolded Projections As Match.
  Record seal {A : Type} (f : A) : Type := Build_seal { unseal : A;  seal_eq : @eq A unseal f }.
  Global Arguments unseal {_ _} _ : assert.
  Global Arguments seal_eq {_ _} _ : assert.

  #[projections(primitive=yes)]
  Structure bi := Bi {
    bi_car :> Type;
    bi_forall : forall A : Type, (A -> bi_car) -> bi_car;
  }.
  Bind Scope bi_scope with bi_car.
  Global Arguments bi_car : simpl never.
  Global Arguments bi_forall {PROP _} _ : simpl never, rename.


  Record heapProp := HeapProp { heapProp_holds :> Prop }.
  Global Arguments heapProp_holds : simpl never.

  Definition heapProp_forall_def {A} (Ψ : A -> heapProp) : heapProp :=
    {| heapProp_holds := forall a, Ψ a |}.
  Definition heapProp_forall_aux : seal (@heapProp_forall_def). Proof. by eexists. Qed.
  Definition heapProp_forall {A} := unseal heapProp_forall_aux A.
  Definition heapProp_forall_unseal :
    @heapProp_forall = @heapProp_forall_def := seal_eq heapProp_forall_aux.

  Definition heapPropI : bi := {| bi_car := heapProp; bi_forall := @heapProp_forall |}.

  Axiom P : heapPropI.

  Goal forall (A : Type) (φ : A -> Prop), (bi_forall (fun a : A => P)).
  Proof.
    intros A φ.
    Succeed (progress unfold bi_forall); (progress simpl).
    progress rewrite /bi_forall.
  Abort.
End R.
