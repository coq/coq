(* Check that the analysis of projectable rel's in an evar instance is up to
   aliases *)

Require Import List.

Definition compose (A B C : Type) (g : B -> C) (f : A -> B) : A -> C :=
  fun x : A => g(f x).

Definition map_fuse' :
  forall (A B C : Type) (g : B -> C) (f : A -> B) (xs : list A),
    (map g (map f xs)) = map (compose _ _ _ g f) xs
    :=
    fun A B C g f =>
      (fix loop (ys : list A) {struct ys} :=
        match ys as ys return (map g (map f ys)) = map (compose _ _ _ g f) ys
        with
        | nil => refl_equal nil
        | x :: xs =>
           match loop xs in eq _ a return eq _  ((g (f x)) :: a) with
            | refl_equal => refl_equal (map g (map f (x :: xs)))
           end
        end).
