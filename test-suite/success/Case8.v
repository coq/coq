(* Check dependencies in the matching predicate (was failing in V8.0pl1) *)

Inductive t : forall x : 0 = 0, x = x -> Prop :=
    c : forall x : 0 = 0, t x (refl_equal x).

Definition a (x : t _ (refl_equal (refl_equal 0))) :=
  match x return match x with
                 | c y => Prop
                 end with
  | c y => y = y
  end.
