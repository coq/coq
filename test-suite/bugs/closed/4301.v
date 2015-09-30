Set Universe Polymorphism.

Module Type Foo.
  Parameter U : Type.
End Foo.

(* Module Lower (X : Foo). *)
(*   Definition U' : Prop := X.U@{Prop}. *)
(* End Lower. *)
(* Module Lower (X : Foo with Definition U := Prop). *)
(*   Definition U' := X.U@{Prop}. *)
(* End Lower. *)
Module Lower (X : Foo with Definition U := True).
  (* Definition U' : Prop := X.U. *)
End Lower.

Module M : Foo.
  Definition U := nat : Type@{i}. 
End M.
