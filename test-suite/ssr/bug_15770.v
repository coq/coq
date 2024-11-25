Require Import Corelib.ssr.ssreflect.

Axiom xget : forall {T} (P : T -> Prop), T.

Variant xget_spec {T} (P : T -> Prop) : T -> Prop -> Type :=
| XGetSome x of P x : xget_spec P x True.

Axiom xgetP : forall {T} (P : T -> Prop), xget_spec P (xget P) (P (xget P)).

Lemma xgetPex {T} (P : T -> Prop) : P (xget P).
Proof.
case: xgetP.
constructor.
Qed.
