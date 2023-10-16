Set Warnings "+all".
#[deprecated(since="1")] Notation a := id.

Goal False.
Proof.
let x := fresh "a" in
idtac.
(* In 8.18.0, it was:
Warning: Notation a is deprecated since 1.
[deprecated-syntactic-definition-since-1,deprecated-since-1,deprecated-syntactic-definition,deprecated,default]
*)
Abort.
