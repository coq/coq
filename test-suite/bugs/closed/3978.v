Require Import Structures.OrderedType.  
Require Import Structures.OrderedTypeEx.

Module Type M. Parameter X : Type.      

Declare Module Export XOrd : OrderedType
  with Definition t := X
  with Definition eq := @Logic.eq X.
End M.

Module M' : M.
  Definition X := nat.

  Module XOrd := Nat_as_OT.
End M'.

Module Type MyOt.
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
End MyOt.

Module Type M2. Parameter X : Type.      

Declare Module Export XOrd : MyOt
  with Definition t := X
  with Definition eq := @Logic.eq X.
End M2.
