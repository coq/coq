(* This used to succeed by producing an ill-typed term in v8.2 *)

Fail Lemma u: forall A : Prop, (exist _ A A) = (exist _ A A).
