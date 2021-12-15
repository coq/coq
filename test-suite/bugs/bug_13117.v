
Class A := {}.

Class B (x:A) := {}.
Class B' (a:=A) (x:a) := {}.

Fail Definition foo a `{B a} := 0.
Definition foo a `{B' a} := 0.

Record C (x:A) := {}.
Existing Class C.

Fail Definition bar a `{C a} := 0.


Definition X := Type.

Class Y (x:X) := {}.

Definition before `{Y Set} := 0.

Existing Class X.
Fail Definition after `{Y Set} := 0.
