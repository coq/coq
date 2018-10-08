Notation prop_fun x y := (fun (x : Prop) => y).
Definition foo := fun (p : Prop) => p.
Definition bar := fun (_ : Prop) => O.
Print foo.
Print bar.
