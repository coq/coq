
Set Universe Polymorphism.
Module Type T.
  Axiom foo@{u v|u < v} : Type@{v}.
End T.

Module M : T with Definition foo@{u v} := Type@{u} : Type@{v}.
  Definition foo@{u v} := Type@{u} : Type@{v}.
End M.

Fail Module M' : T with Definition foo := Type.

(* Without the binder expression we have to do trickery to get the
   universes in the right order. *)
Module M' : T with Definition foo := let t := Type in t.
