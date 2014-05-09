Goal forall (O obj : Type) (f : O -> obj) (x : O) (e : x = x)
     (T : obj -> obj -> Type) (m : forall x0 : obj, T x0 x0),
   match eq_sym e in (_ = y) return (T (f y) (f x)) with
   | eq_refl => m (f x)
   end = m (f x).
intros.
try case e.
(* Toplevel input, characters 19-25:
Error: Cannot instantiate metavariable P of type
"forall a : O, x = a -> Prop" with abstraction
"fun (x : O) (e : x = x) =>
 match eq_sym e in (_ = y) return (T (f y) (f x)) with
 | eq_refl => m (f x)
 end = m (f x)" of incompatible type "forall x : O, x = x -> Prop". *)
