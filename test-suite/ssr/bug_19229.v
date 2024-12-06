From Corelib.ssr Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module isSub.
(* val_subdef being a primitive projections is what makes it fail *)
#[projections(primitive)]
Record axioms_ T (P : pred T) sub_sort : Type :=
  Axioms_ { val_subdef : sub_sort -> T }.
Definition phant_Build T (P : pred T) sub_sort (val_subdef : sub_sort -> T) :=
  @isSub.Axioms_ T P sub_sort val_subdef.
End isSub.

Module SubType.
Record axioms_ T (P : pred T) S : Type := Class
  { ssralg_isSub_mixin : isSub.axioms_ P S }.
Record type T (P : pred T) : Type :=
  Pack { sort : Type; class : @SubType.axioms_ T P sort }.
Definition phant_on_ T (P : pred T) (S : type P) (_ : phant (sort S)) :=
  class S.
Notation on elpi_ctx_entry_1_was_T_ :=
  (phant_on_ (Phant _) : axioms_ _ elpi_ctx_entry_1_was_T_).
Module Exports.
Coercion sort : type >-> Sortclass.
Coercion ssralg_isSub_mixin : axioms_ >-> isSub.axioms_.
Definition val_subdef T (P : pred T) (s : type P) :=
  isSub.val_subdef (SubType.ssralg_isSub_mixin (class s)).
End Exports.
End SubType.
Export SubType.Exports.

(* We need a canonical projection so that rewrite can do keyd matching modulo CS inference *)
Notation val := ((SubType.on _).(isSub.val_subdef)).
Notation "\val" := ((SubType.on _).(isSub.val_subdef)) (only parsing).
Notation "\val" := ((_).(isSub.val_subdef)) (only printing).

Module isNmodule.
Record axioms_ V : Type := Axioms_ { add : V -> V -> V }.
Definition phant_Build V (add : V -> V -> V) := Axioms_ add.
End isNmodule.

Module Nmodule.
Record axioms_ (V : Type) : Type := Class
  { ssralg_isNmodule_mixin : isNmodule.axioms_ V } as record.
Record type : Type :=
    Pack { sort : Type; class : Nmodule.axioms_ sort }.
Module Exports.
Notation nmodType := Nmodule.type.
Coercion sort : type >-> Sortclass.
Definition add (s : Nmodule.type) :=
  isNmodule.add (Nmodule.ssralg_isNmodule_mixin (Nmodule.class s)).
End Exports.
End Nmodule.
Export Nmodule.Exports.

Module isSemiAdditive.
Variant axioms_ (U V : Nmodule.type)
    (apply : forall _ : Nmodule.sort U, Nmodule.sort V) : Type := Axioms_.
Definition phant_Build
  (U V : Nmodule.type) (apply : forall _ : Nmodule.sort U, Nmodule.sort V) :=
  @isSemiAdditive.Axioms_ U V apply.
End isSemiAdditive.

Module Additive.
Record axioms_ (U V : nmodType) (f : U -> V) : Type := Class
  { ssralg_isSemiAdditive_mixin : isSemiAdditive.axioms_ f } as record.
Record type (U V : nmodType) : Type := Pack
  { sort : U -> V;  class : Additive.axioms_ sort }.
Module Exports.
Coercion sort : type >-> Funclass.
End Exports.
End Additive.
Export Additive.Exports.

Lemma raddfD U V (f : Additive.type U V) : {morph f : x y / add x y}.
Admitted.

Module isAddClosed.
Variant axioms_ (V : Nmodule.type)
(S : @pred_sort (Nmodule.sort V) (predPredType (Nmodule.sort V))) : Type :=
    Axioms_.
Definition phant_Build (V : Nmodule.type)
    (S : pred_sort (predPredType (Nmodule.sort V))) := Axioms_ S.
End isAddClosed.

Module AddClosed.
Record axioms_ (V : Nmodule.type)
    (S : pred_sort (predPredType (Nmodule.sort V))) : Type :=
  Class { ssralg_isAddClosed_mixin : isAddClosed.axioms_ S }.
Record type (V : Nmodule.type) : Type := Pack
  { sort : pred_sort (predPredType (Nmodule.sort V));
    _ : AddClosed.axioms_ sort }.
End AddClosed.

Module isSubNmodule.
Definition isSubNmodule_U__canonical__ssralg_SubType (V : nmodType) (S : pred V)
    (U : Type) (local_mixin_ssralg_isSub : isSub.axioms_ S U) :=
  {|
    SubType.sort := U;
    SubType.class := {| SubType.ssralg_isSub_mixin := local_mixin_ssralg_isSub |}
  |}.
Definition isSubNmodule_U__canonical__ssralg_Nmodule (U : Type)
    (local_mixin_ssralg_isNmodule : isNmodule.axioms_ U) :=
  {|
    Nmodule.sort := U;
    Nmodule.class := {| Nmodule.ssralg_isNmodule_mixin := local_mixin_ssralg_isNmodule |}
  |}.
Record axioms_ (V : nmodType) (S : pred V) (U : Type)
    (local_mixin_ssralg_isSub : isSub.axioms_ S U)
    (local_mixin_ssralg_isNmodule : isNmodule.axioms_ U) : Type :=
  Axioms_ {  }.
Definition phant_Build (V : nmodType) (S : pred V) (U : Type)
    (m : isSub.axioms_ S U) (m0 : isNmodule.axioms_ U)
  := Axioms_ m m0.
End isSubNmodule.

Module SubNmodule.
Record axioms_ (V : nmodType) (S : pred V) (U : Type) : Type := Class
  { ssralg_isSub_mixin :> isSub.axioms_ S U;
    ssralg_isNmodule_mixin :> isNmodule.axioms_ U;
    ssralg_isSubNmodule_mixin :> isSubNmodule.axioms_ ssralg_isSub_mixin
                                  ssralg_isNmodule_mixin }.
Record type (V : nmodType) (S : pred V) : Type := Pack
  { sort :> Type;  class : SubNmodule.axioms_ S sort }.
Module Exports.
Coercion ssralg_SubNmodule_class__to__ssralg_Nmodule_class
    (V : nmodType) (S : pred V) (U : Type) (c : SubNmodule.axioms_ S U) :=
  {| Nmodule.ssralg_isNmodule_mixin := c |}.
Coercion ssralg_SubNmodule__to__ssralg_Nmodule
    (V : nmodType) (S : pred V) (s : SubNmodule.type S) :=
  {| Nmodule.sort := s; Nmodule.class := SubNmodule.class s |}.
Coercion ssralg_SubNmodule_class__to__ssralg_SubType_class
    (V : nmodType) (S : pred V) (U : Type) (c : SubNmodule.axioms_ S U) :=
  {| SubType.ssralg_isSub_mixin := c |}.
Coercion ssralg_SubNmodule__to__ssralg_SubType
    (V : nmodType) (S : pred V) (s : SubNmodule.type S) :=
  {| SubType.sort := s; SubType.class := SubNmodule.class s |}.
Canonical join_ssralg_SubNmodule_between_ssralg_Nmodule_and_ssralg_SubType
    (V : nmodType) (S : pred V) (U : SubNmodule.type S) :=
  {| SubType.sort := U; SubType.class := SubType.class U |}.
End Exports.
End SubNmodule.
Export SubNmodule.Exports.

Definition HB_unnamed_factory_0 (V : Nmodule.type) (S : pred (Nmodule.sort V))
    (U : @SubNmodule.type V S) :=
  @isSemiAdditive.Axioms_ U V
    (@isSub.val_subdef _ _ _
       (SubType.ssralg_isSub_mixin (SubType.phant_on_ (Phant _)))).

Canonical isSub_val_subdef__canonical__ssralg_Additive
    (V : Nmodule.type) (S : pred (Nmodule.sort V)) (U : @SubNmodule.type V S) :=
  @Additive.Pack (@ssralg_SubNmodule__to__ssralg_Nmodule V S U) V
    (isSub.val_subdef _) (Additive.Class (HB_unnamed_factory_0 U)).

Parameter V : Nmodule.type.
Parameter S : pred (Nmodule.sort V).
Parameter U : Type.
Parameter local_mixin_ssralg_isSub : isSub.axioms_ S U.

Canonical Builders_18_U__canonical__ssralg_SubType :=
  @SubType.Pack (Nmodule.sort V) S U
    (@SubType.Class (Nmodule.sort V) S U local_mixin_ssralg_isSub).

Definition HB_unnamed_factory_1 := @isAddClosed.phant_Build V S.

Canonical Builders_4_S__canonical__ssralg_AddClosed :=
  @AddClosed.Pack V S (AddClosed.Class HB_unnamed_factory_1).

Parameter addU : U -> U -> U.

Definition HB_unnamed_factory_2 := @isNmodule.phant_Build U addU.

Canonical Builders_4_U__canonical__ssralg_Nmodule :=
  @Nmodule.Pack U (Nmodule.Class HB_unnamed_factory_2).

Definition HB_unnamed_factory_3 :=
  @isSubNmodule.phant_Build V S U local_mixin_ssralg_isSub HB_unnamed_factory_2.

Canonical Builders_4_U__canonical__ssralg_SubNmodule :=
  @SubNmodule.Pack V S U (SubNmodule.Class HB_unnamed_factory_3).

Lemma mulrDl (x y : U) : \val (add x y) = \val (add y x).
Proof.
rewrite raddfD.  (* but "rewrite [LHS]raddfD." works *)
Abort.
