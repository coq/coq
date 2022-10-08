(* this bug was a proof of False *)

Set Warnings "+no-template-universe".

(* when we require template poly Coq recognizes that it's not allowed *)
Fail
  Inductive foo@{i} (A:Type@{i}) : Type@{i+1} := bar (X:Type@{i}) : foo A.

(* variants with letin *)
Fail
 Inductive foo@{i}  (T:=Type@{i}:Type@{i+1}) (A:Type@{i}) : Type@{i+1} := bar (X:T) : foo A.

Fail
 Record foo@{i}  (T:=Type@{i}:Type@{i+1}) (A:Type@{i}) : Type@{i+1} := bar { X:T }.


(* no implicit template poly, no explicit universe annotations *)
Inductive foo (A:Type) := bar X : foo X -> foo A | nonempty.
Arguments nonempty {_}.

Fail Check foo nat : Type@{foo.u0}.
(* template poly didn't activate *)

Definition U := Type.
Definition A : U := foo nat.

Fail Definition down : U -> A := fun u => bar nat u nonempty.
(* this is the one where it's important that it fails *)
