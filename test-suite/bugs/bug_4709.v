
(** Bug 4709 https://coq.inria.fr/bug/4709
    Extraction wasn't reducing primitive projections in types. *)

Require Extraction.

Set Primitive Projections.

Record t := Foo { foo : Type }.
Definition ty := foo (Foo nat).

(* Without proper reduction of primitive projections in
   [extract_type], the type [ty] was extracted as [Tunknown].
   Let's check it isn't the case anymore. *)

Parameter check : nat.
Extract Constant check => "(O:ty)".
Extraction TestCompile ty check.
