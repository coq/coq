

Class Foo := foo { a : nat; b : bool }.

Fail #[export] Instance bla : Foo := { b:= true }.

#[refine, export] Instance bla : Foo := { b:= true }.
Proof.
exact 0.
Defined.

#[export] Instance bli : Foo := { a:=1; b := false}.
Check bli.

Fail #[program, refine] Instance bla : Foo := {b := true}.

#[program, export] Instance blo : Foo := {b := true}.
Next Obligation. exact 2. Qed.
Check blo.

#[refine, export] Instance xbar : Foo := {a:=4; b:=true}.
Proof. Qed.
Check xbar.
