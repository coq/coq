Inductive SFalse : SProp := .
Definition adjust_of_sprop {A} {x y : A} (pf : x <> y) : x <> y
  := fun e : x = y => SFalse_ind (fun _ => False) (match pf e with end).

Definition adjust_of_sprop_idempotent {A x y pf} : @adjust_of_sprop A x y (@adjust_of_sprop A x y pf) = @adjust_of_sprop A x y pf.
Proof. cbv [adjust_of_sprop]; reflexivity. Defined.
Definition adjust_of_sprop_idempotent' {A x y pf} : @adjust_of_sprop A x y (@adjust_of_sprop A x y pf) = @adjust_of_sprop A x y pf
  := Eval cbv in @adjust_of_sprop_idempotent A x y pf.

Inductive sF : SProp := .

Definition ff (x y:sF) : match x return nat with end = match y with end := eq_refl.
