

Class Foo := foo { a : nat; b : bool }.

Fail Instance bla : Foo := { b:= true }.

#[refine] Instance bla : Foo := { b:= true }.
Proof.
exact 0.
Defined.

Instance bli : Foo := { a:=1; b := false}.
Check bli.

Fail #[program, refine] Instance bla : Foo := {b := true}.

#[program] Instance blo : Foo := {b := true}.
Next Obligation. exact 2. Qed.
Check blo.

#[refine] Instance xbar : Foo := {a:=4; b:=true}.
Proof. Qed.
Check xbar.
