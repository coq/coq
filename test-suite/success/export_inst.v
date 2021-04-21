Class Foo.

Module Foo.

#[export]
Instance F : Foo := {}.

End Foo.

Fail Definition foo_test := let _ : Foo := _ in tt.

Import Foo.

Definition foo_test := let _ : Foo := _ in tt.

Class Bar.

Module Bar.

Section Bar.

Variable b : Bar.

#[export] Instance B : Bar := {}.

(* Cannot declare variables as export instances *)
Fail #[export] Existing Instance b.

End Bar.

Definition bar_test := let _ : Bar := _ in tt.

End Bar.

Fail Definition bar_test := let _ : Bar := _ in tt.

Import Bar.

Definition bar_test := let _ : Bar := _ in tt.
