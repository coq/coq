Require Import MSets.
Require Import Utf8.
Require FMaps.
Import Orders.

Set Implicit Arguments.

(* Conversion between the two kinds of OrderedType. *)
Module OTconvert (O : OrderedType) : OrderedType.OrderedType
          with Definition t := O.t
          with Definition eq := O.eq
          with Definition lt := O.lt.

  Definition t := O.t.
  Definition eq := O.eq.
  Definition lt := O.lt.
  Definition eq_refl := reflexivity.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Admitted.
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Admitted.
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Admitted.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Admitted.
  Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
  Admitted.
  Definition eq_dec := O.eq_dec.
End OTconvert.

(* Dependent Maps *)
Module Type Interface (X : OrderedType).
  Module Dom : MSetInterface.SetsOn(X) with Definition elt := X.t := MSetAVL.Make(X).
  Definition key := X.t.
  Parameter t : forall (A : Type) (dom : Dom.t), Type.
  Parameter constant : forall A dom, A -> t A dom.
End Interface.

Module DepMap (X : OrderedType) : (Interface X) with Definition key := X.t.
  Module Dom := MSetAVL.Make(X).
  Module XOT := OTconvert X.
  Module S := FMapList.Make(XOT).
  Definition key := X.t.
  Definition OK {A} dom (map : S.t A) := ∀ x, S.In x map <-> Dom.In x dom.
  Definition t := fun A dom => { map : S.t A | OK dom map}.
  Corollary constant_OK : forall A dom v, OK dom (Dom.fold (fun x m => S.add x v m) dom (S.empty A)).
  Admitted.
  Definition constant (A : Type) dom (v : A) : t A dom :=
    exist (OK dom) (Dom.fold (fun x m => S.add x v m) dom (@S.empty A)) (constant_OK dom v).
End DepMap.


Declare Module Signal : OrderedType.
Module S := DepMap(Signal).
Notation "∅" := (S.constant _ false).

Definition I2Kt {dom} (E : S.t (option bool) dom) : S.t bool dom := S.constant dom false. 
Arguments I2Kt {dom} E.

Inductive cmd := nothing.

Definition semantics (A T₁ T₂ : Type) := forall dom, T₁ -> S.t A dom -> S.t A dom -> nat -> T₂ -> Prop.

Inductive LBS : semantics bool cmd cmd := LBSnothing dom (E : S.t bool dom) : LBS nothing E ∅ 0 nothing.

Theorem CBS_LBS : forall dom p (E E' : S.t _ dom) k p', LBS p (I2Kt E) (I2Kt E') k p'.
admit.
Defined.

Print Assumptions CBS_LBS.
