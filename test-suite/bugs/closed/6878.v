
Set Universe Polymorphism.
Module Type T.
  Axiom foo : Prop.
End T.

(** Used to anomaly *)
Fail Module M : T with Definition foo := Type.
