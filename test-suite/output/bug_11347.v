Require Import Setoid.

Lemma foo (b:unit) : (match b with tt => fun  (C :  Prop) => C end) True.
Proof.
  Fail setoid_rewrite or_comm. (* or any lemma that can be used for rewriting *)
Abort.
