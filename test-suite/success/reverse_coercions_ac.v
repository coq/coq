Set Implicit Arguments.

Class Inhab (A:Type) : Prop :=
  { inhab: exists (x:A), True }.

Record IType : Type := IType_make
  { IType_type :> Type;
    IType_inhab : Inhab IType_type }.

Canonical default_IType t ct : IType := @IType_make t ct.

Arguments IType_make IType_type {IType_inhab}.

Global Instance Inhab_IType : forall (A:IType), Inhab A.
Proof using. constructor. apply IType_inhab. Defined.

Parameter P : Type -> Prop.

(** A [IType] can be provided where an type [A] with a proof of [Inhab A] is expected. *)
Parameter K : forall (A:Type) (IA:Inhab A), P A.
Lemma testK : forall (A:IType), P A.
Proof using. intros. eapply K. eauto with typeclass_instances. Qed.

(** A type [A] can be provided where a [IType] is expected, by wrapping it with [IType_make]. *)
Parameter T : forall (A:IType), P A.
Lemma testT : forall (A:Type) (IA:Inhab A), P A.
Proof using. intros. eapply (T A). Qed.

(* Above, it would be nice to write [eapply (T A)], or just [eapply T].
   For that, we'd need to coerce [A:Type] to the type [IType]
   by applying on-the-fly the operation [IType_make A _]. Thus, we need something like:
   [Coercion (fun (A:Type) => IType_make A _) : Sortclass >-> IType.]
  Would that be possible?

  I understand that [IType_type] is already a reverse coercion from [IType] to [Type],
  but I don't see why it would necessarily cause trouble to have cycles
  in the coercion graphs. *)
