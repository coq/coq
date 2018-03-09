
Set Primitive Projections.

Record R := C { p : nat }.
(* R is defined
p is defined *)

Unset Primitive Projections.
Record R' := C' { p' : nat }.



Fail Definition f := fix f (x : R) : nat := p x.
(** Not allowed to make fixpoint defs on (non-recursive) records
  having eta *)

Fail Definition f := fix f (x : R') : nat := p' x.
(** Even without eta (R' is not primitive here), as long as they're
  found to be BiFinite (non-recursive), we disallow it *)

(*

(* Subject reduction failure example, if we allowed fixpoints *)

Set Primitive Projections.

Record R := C { p : nat }.

Definition f := fix f (x : R) : nat := p x.

(* eta rule for R *)
Definition Rtr (P : R -> Type) x (v : P (C (p x))) : P x
 := v.

Definition goal := forall x, f x = p x.

(* when we compute the Rtr away typechecking will fail *)
Definition thing : goal := fun x =>
(Rtr (fun x => f x = p x) x (eq_refl _)).

Definition thing' := Eval compute in thing.

Fail Check (thing = thing').
(*
The command has indeed failed with message:
The term "thing'" has type "forall x : R, (let (p) := x in p) = (let (p) := x in p)"
while it is expected to have type "goal" (cannot unify "(let (p) := x in p) = (let (p) := x in p)"
and "f x = p x").
*)

Definition thing_refl := eq_refl thing.

Fail Definition thing_refl' := Eval compute in thing_refl.
(*
The command has indeed failed with message:
Illegal application:
The term "@eq_refl" of type "forall (A : Type) (x : A), x = x"
cannot be applied to the terms
 "forall x : R, (fix f (x0 : R) : nat := let (p) := x0 in p) x = (let (p) := x in p)" : "Prop"
 "fun x : R => eq_refl" : "forall x : R, (let (p) := x in p) = (let (p) := x in p)"
The 2nd term has type "forall x : R, (let (p) := x in p) = (let (p) := x in p)"
which should be coercible to
 "forall x : R, (fix f (x0 : R) : nat := let (p) := x0 in p) x = (let (p) := x in p)".
 *)

Definition more_refls : thing_refl = thing_refl.
Proof.
  compute. reflexivity.
Fail Defined. Abort.
 *)
