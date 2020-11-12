Polymorphic Inductive path {A : Type} (x : A) : A -> Type :=
  refl : path x x.

Goal False.
Proof.
simple refine (let H : False := _ in _).
+ exact_no_check I.
+ assert (path true false -> path false true).
  (** Create a dummy polymorphic side-effect *)
  {
    intro IHn.
    rewrite IHn.
    reflexivity.
  }
  exact H.
Fail Qed.
Abort.
