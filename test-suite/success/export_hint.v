Create HintDb foo.

Module Foo.

Axiom F : False.

#[export]
Hint Immediate F : foo.

End Foo.

Goal False.
Proof.
Fail solve [auto with foo].
Abort.

Import Foo.

Goal False.
Proof.
auto with foo.
Qed.
