(* -*- coq-prog-args: ("-noinit"); -*- *)

Example simple_cbn := Eval cbn in (fun x:Set => x).

Definition id {A} (x:A) := x.
Definition set := Eval lazy in id Set.

Compute id Set.

Require Import Prelude.

Goal Prop.
  let c := eval unfold set in set in
  constr_eq c Set.
Abort.
