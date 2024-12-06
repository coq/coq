
From Stdlib Require Import Morphisms.

Search is:Instance [ Reflexive | Symmetric ].

Module Bug12525.
  (* This was revealing a kernel bug with delta-resolution *)
  Module A. Axiom a:Prop. Axiom b:a. End A.
  Module B. Include A. End B.
  Module M.
    Search B.a.
  End M.
End Bug12525.

From Stdlib Require Lia.

Module Bug12647.
  (* Similar to #12525 *)
  Module Type Foo.
  Axiom P : nat -> Prop.
  Axiom L : P 0.
  End Foo.

  Module Bar (F : Foo).
  Search F.P.
  End Bar.
End Bug12647.

Module WithCoercions.
  Search headconcl:(_ + _) inside Datatypes.
  Coercion Some_nat := @Some nat.
  Axiom f : None = 0.
  Search (None = 0).
End WithCoercions.

From Stdlib Require Import List.

Module Wish13349.
Search partition "1" inside List.
End Wish13349.
