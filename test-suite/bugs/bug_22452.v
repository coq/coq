Module M0. Definition n := true. End M0.

Module Outer.
  Module Type TI. Parameter Inline n : bool. End TI.
  Module F (X : TI). Module Inner := X. End F.
  Module M105. Include M0. End M105.
  Module Sub := Outer.F Outer.M105.
End Outer.

Include Outer.

Definition bug : Sub.Inner.n = M0.n := eq_refl.
(* Ill-formed constant Sub.Inner.n: expected canonical name Top.M0.n but found Top.Outer.M105.n *)
