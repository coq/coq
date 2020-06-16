Require Import ssreflect ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom finGroupType : Type.
Axiom group : finGroupType -> Type.
Axiom abelian : forall gT : finGroupType, group gT -> Prop.
Arguments abelian {_} _.
Axiom carrier : finGroupType -> Type.
Coercion carrier : finGroupType >-> Sortclass.
Axiom mem : forall gT : finGroupType, gT -> group gT -> Prop.
Arguments mem {_} _ _.
Axiom mul : forall gT : finGroupType, gT -> gT -> gT.
Arguments mul {_} _ _.
Definition centralised gT (G : group gT) (x : gT) := forall y, mul x y = mul y x.
Arguments centralised {gT} _.
Axiom b : bool.

Axiom centsP : forall (gT : finGroupType) (A B : group gT),
  reflect (forall a, mem a A -> centralised B a) b.
Arguments centsP {_ _ _}.

Lemma commute_abelian (gT : finGroupType) (G : group gT)
  (G_abelian : abelian G) (g g' : gT) (gG : mem g  G) (g'G : mem g'  G) :
  mul g g' = mul g' g.
Proof.
Fail rewrite (centsP _). (* fails but without an anomaly *)
Abort.
