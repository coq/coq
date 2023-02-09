(* This used to fail because Foo_VeryLongFieldNameOfFoo was
   interpreted as a notation variable in the reversibility test *)

Local Reserved Notation "'F'".
Record Foo :=
  {
    Foo_VeryLongFieldNameOfFoo :> Type where "'F'" := Foo_VeryLongFieldNameOfFoo;
    Foo_Law : F = F
  }.
