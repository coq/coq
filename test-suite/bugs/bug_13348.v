Generalizable All Variables.

Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
Arguments populate {_} _.

Set Mangle Names.
Axioms _0 _1 _2 : Prop.

Instance impl_inhabited {A} {B} {_3:Inhabited B} : Inhabited (A -> B)
  := populate (fun _ => inhabitant).
