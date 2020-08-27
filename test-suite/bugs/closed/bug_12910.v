Class Foo := foo : True.
Instance i : Foo. Proof. exact I. Qed.
Definition j : Foo. Proof. exact I. Qed.

Inductive bla : Foo -> Prop := .

Definition xx : bla _ -> _ := fun x : bla j => x.
(* Error: Found type "bla j" where "bla i" was expected. *)
