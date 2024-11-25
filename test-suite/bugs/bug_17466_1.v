
Require Import Corelib.Setoids.Setoid.

Set Implicit Arguments.

Record PartialOrder : Type :=
{ po_car :> Type
; le : po_car -> po_car -> Prop
; monotone : (po_car -> po_car) -> Prop
}.
Notation "x <= y" := (le _ x y).

Section PartialOrder.

Variable X : PartialOrder.

Lemma monotone_def : forall f, monotone X f <-> (forall x y, x <= y -> (f x) <= (f y)).
Admitted.

End PartialOrder.
Set Firstorder Depth 5.

Record SemiLattice : Type :=
{ po :> PartialOrder
; meet : po -> po -> po

}.

Arguments meet [s].

Axiom X : SemiLattice.

Lemma meet_monotone_l : forall a : X, monotone X (fun x => meet x a).
Admitted.

Lemma meet_le_compat : forall w x y z : X, w<=y -> meet w x <= meet y x.
Proof.
 intros.
 solve [firstorder using meet_monotone_l, monotone_def].
Qed.
