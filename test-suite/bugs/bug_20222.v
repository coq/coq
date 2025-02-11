Polymorphic Definition foo@{u|} (A : Type@{u}) (a b: A) (p : a = b) : True :=
match p in (_ = a1) with
| eq_refl => I
end.
(* Universe constraints are not implied by the ones declared: u <= eq.u0 *)
