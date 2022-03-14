(* coq-prog-args: ("-async-proofs" "off") *)

Definition T1 (X : Type) : Type := list X.
Coercion C1 (X: Type) (A : T1 X) : Prop := True.
(* Works fine. *)

Goal True = (nil : T1 nat).
Proof.
  Show.
  trivial.
Qed.

Definition T2 (X : Type) : Type := list X.
Section S.
  Context (X : Type).
  Coercion C2 (A : T2 X) : Prop := True.
End S.

Goal True = (nil : T2 nat).     (* The coercion works... *)
Proof.
  Show.
  trivial.
Qed.
