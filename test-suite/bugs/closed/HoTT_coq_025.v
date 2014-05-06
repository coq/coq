Module monomorphic.
  Class Inhabited (A : Type) : Prop := populate { _ : A }.
  Arguments populate {_} _.

  Instance prod_inhabited {A B : Type} (iA : Inhabited A)
           (iB : Inhabited B) :   Inhabited (A * B) :=
    match iA, iB with
      | populate x, populate y => populate (x,y)
    end.
  (* Error: In environment
A : Type
B : Type
iA : Inhabited A
iB : Inhabited B
The term "(A * B)%type" has type "Type" while it is expected to have type
"Prop". *)
End monomorphic.

Module polymorphic.
  Set Universe Polymorphism.
  Class Inhabited (A : Type) : Prop := populate { _ : A }.
  Arguments populate {_} _.

  Instance prod_inhabited {A B : Type} (iA : Inhabited A)
           (iB : Inhabited B) :   Inhabited (A * B) :=
    match iA, iB with
      | populate x, populate y => populate (x,y)
    end.
End polymorphic.
