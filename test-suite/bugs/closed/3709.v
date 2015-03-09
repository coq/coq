Require Import TestSuite.admit.
Module NonPrim.
  Unset Primitive Projections.
  Record hProp := hp { hproptype :> Type }.
  Goal forall (h : (Type -> hProp) -> (Type -> hProp)) k f,
         (forall y, h y = y) ->
         h (fun b : Type => {| hproptype := f b |}) = k.
  Proof.
    intros h k f H.
    etransitivity.
    apply H.
    admit.
  Defined.
End NonPrim.
Module Prim.
  Set Primitive Projections.
  Record hProp := hp { hproptype :> Type }.
  Goal forall (h : (Type -> hProp) -> (Type -> hProp)) k f,
         (forall y, h y = y) ->
         h (fun b : Type => {| hproptype := f b |}) = k.
  Proof.
    intros h k f H.
    etransitivity.
    apply H.
