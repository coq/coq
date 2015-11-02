(* -*- coq-prog-args: ("-emacs" "-compat" "8.4") -*- *)
Require Import Equality List.
Unset Strict Universe Declaration.
Inductive Foo I A := foo (B : Type) : A -> I B -> Foo I A.
Definition Family := Type -> Type.
Definition fooFamily family : Family := Foo family.
Inductive Empty {T} : T -> Prop := .
Theorem empty (family : Family) (a : fold_right prod unit (map (Foo family) nil)) (b : unit) :
  Empty (a, b) -> False.
Proof.
  intro e.
  dependent induction e.
Qed.