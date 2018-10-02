Section foo.
  Let foo := Type.
  Definition bar : foo -> foo := @id _.
  Goal False.
    subst foo.
    Fail pose bar as f.
    (* simpl in f. *)
