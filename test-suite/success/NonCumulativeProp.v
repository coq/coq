Unset Cumulative Prop.

Fail Check fun P:Prop => P:Set.

Inductive Box (A:Prop) : Set := box (_:A).

Check Box True.

(* template can't be instantiated with Prop *)
Inductive TBox (A:Type) : Type := tbox (_:A).

Check TBox nat : Set.

Check TBox Set.

Fail Check TBox True.
