Module ExternRewrite.

Parameter a b c : unit.
Parameter P : unit -> Prop.
Axiom Eac : a = c.
Axiom (Pab : P a -> P b).

Ltac Xtac :=
  match goal with
  | [ H : (True -> P a) |- _  ] => rewrite Eac in H
  end.

Create HintDb db.
#[local] Hint Resolve Pab : db.
#[local] Hint Extern 0 => Xtac : db.

Goal True -> (True -> P a) -> P b.
Proof.
  auto with db nocore.
Qed.

End ExternRewrite.

Module ExternClear.

Parameter P Q R : Prop.
Axiom (HQR : Q -> R).
Axiom (HP : P).

Ltac Xtac := match goal with [H : _ |- _] => clear H end.

Create HintDb db.
#[local] Hint Resolve HQR : db.
#[local] Hint Resolve HP : db.
#[local] Hint Extern 0 => Xtac : db.

Goal (P -> Q) -> R.
Proof.
  auto with db nocore.
Qed.

End ExternClear.
