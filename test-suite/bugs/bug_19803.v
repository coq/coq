Module Equality.

Record type : Type := Pack { sort : Type }.

End Equality.

Module SubType.

Record type (T : Type) : Type := Pack { sort : Type }.

End SubType.

Definition Top_SubType__canonical__Top_Equality (T : Equality.type) (sT : SubType.type (Equality.sort T)) : Equality.type :=
  @Equality.Pack (@SubType.sort (Equality.sort T) sT).

Module Topological.

Record type : Type := Pack { sort : Type }.

End Topological.

Definition Top_Topological__to__Top_Equality (s : Topological.type) : Equality.type :=
  @Equality.Pack (@Topological.sort s).

Definition weak_topology (S : Type) : Type := S.

Definition Top_weak_topology__canonical__Top_Topological (S : Equality.type) : Topological.type :=
  @Topological.Pack (@weak_topology (Equality.sort S)).

Axiom set_system : Type -> Prop.
Structure filter_on T := FilterType { filter : set_system T; }.
Axiom Filter : forall (T : Type) (F : set_system T), Type.
Axiom filter_class : forall T (F : filter_on T), @Filter T (filter T F).
Axiom nbhs : forall (U : Type) (s : Type), set_system U.

Definition nbhs_filter_on {T : Topological.type} : filter_on (Topological.sort T) :=
  FilterType (Topological.sort T)  (@nbhs (Topological.sort T) ((Topological.sort T))).

Canonical Structure Top_Topological__to__Top_Equality.
Canonical Structure Top_weak_topology__canonical__Top_Topological.
Canonical Structure Top_SubType__canonical__Top_Equality.
Canonical Structure nbhs_filter_on.

Goal forall
  {X : Topological.type}
  {Y : @SubType.type (Topological.sort X)},
  @Filter (@SubType.sort (Topological.sort (Topological.Pack (Topological.sort X))) Y)
    (@nbhs (@SubType.sort (Topological.sort X) Y)
       ( (weak_topology (@SubType.sort (Topological.sort X) Y)))).
Proof.
intros.
(** Check that is_open_canonical_projection correctly expands defined metas *)
autoapply filter_class with typeclass_instances.
Qed.
