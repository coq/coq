(* Check insertion of impossible case when there is no branch at all *)

Inductive eq_true : bool -> Prop :=  is_eq_true : eq_true true.

Check fun H:eq_true false => match H with end : False.

Inductive I : bool -> bool -> Prop := C : I true true.

Check fun x (H:I x false) => match H with end : False.

Check fun x (H:I false x) => match H with end : False.

Inductive I' : bool -> Type := C1  : I' true | C2 : I' true.

Check fun x : I' false => match x with end : False.
