(* Testing recursive notations with binders seen as terms *)

Inductive ftele : Type :=
| fb {T:Type} : T -> ftele
| fr {T} : (T -> ftele) -> ftele.

Fixpoint args ftele : Type :=
  match ftele with
    | fb _ => unit
    | fr f => sigT (fun t => args (f t))
  end.

Definition fpack := sigT args.
Definition pack fp fa : fpack := existT _ fp fa.

Notation "'tele' x .. z := b" :=
  (
    (fun x => ..
                (fun z =>
                   pack
                     (fr (fun x => .. ( fr (fun z => fb b) ) .. ) )
                     (existT _ x .. (existT _ z tt) .. )
                ) ..
    )
  ) (at level 85, x binder, z binder).

Check fun '((y,z):nat*nat) => pack (fr (fun '((y,z):nat*nat) => fb tt))
                                   (existT _ (y,z) tt).

Example test := tele (t : Type) := tt.
Example test' := test nat.
Print test.

Example test2 := tele (t : Type) (x:t) := tt.
Example test2' := test2 nat 0.
Print test2.

Example test3 := tele (t : Type) (y:=0) (x:t) := tt.
Example test3' := test3 nat 0.
Print test3.

Example test4 := tele (t : Type) '((y,z):nat*nat) (x:t) := tt.
Example test4' := test4 nat (1,2) 3.
Print test4.
