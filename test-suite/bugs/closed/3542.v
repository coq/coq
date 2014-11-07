Section foo.
  Context {A:Type} {B : A -> Type}.
  Context (f : forall x, B x).
  Goal True.
    pose (r := fun k => existT (fun g => forall x, f x = g x)
                               (fun x => projT1 (k x)) (fun x => projT2 (k x))).
