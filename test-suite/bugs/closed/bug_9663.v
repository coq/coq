Definition id_depfn S T (f : forall x : S, T x) := f.
Definition idn : nat -> nat := @id_depfn _ _ (fun x => x).
