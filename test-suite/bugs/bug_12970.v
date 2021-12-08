Arguments existT _ & _ _.

Definition f := fun X (A : X -> Type) (P : forall x, A x -> Type) x y =>
        existT (fun f => forall x, P x (f x)) x y : sigT (fun f => forall x, P x (f x)).
