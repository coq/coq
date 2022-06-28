Record myRecord := {
  my_class : Type ;
}.

Fail #[export] Instance my_instance : forall x, my_class x.

Existing Class my_class.

#[export] Instance my_instance : forall x, my_class x. Abort.

Definition my_existing_instance : forall x, my_class x. Admitted.

#[export]
Existing Instance my_existing_instance.

Set Primitive Projections.

Record myOtherRecord := {
  my_other_class : Type ;
}.

Fail #[export] Instance my_other_instance : forall x, my_other_class x.

Existing Class my_other_class.

#[export] Instance my_other_instance : forall x, my_other_class x. Abort.

Definition my_other_existing_instance : forall x, my_other_class x. Admitted.

(* ??? *)
(* Used to be: Constant does not build instances of a declared type class. *)
#[export]
Existing Instance my_other_existing_instance.
