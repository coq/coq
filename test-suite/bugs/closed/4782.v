(* About typing of with bindings *)

Record r : Type := mk_r { type : Type; cond : type -> Prop }.

Inductive p : Prop := consp : forall (e : r) (x : type e), cond e x -> p.

Goal p.
Fail apply consp with (fun _ : bool => mk_r unit (fun x => True)) nil.
