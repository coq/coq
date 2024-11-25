Require Corelib.Setoids.Setoid.
Export Corelib.Classes.Morphisms.
Export Corelib.Setoids.Setoid.

Axiom A : Type.
Axiom equiv : relation A.
Axiom sg_op : A -> A -> A.
Axiom mon_unit : A.
Axiom negate : A -> A.

#[export] Declare Instance sg_setoid : Equivalence equiv.
#[export] Declare Instance sg_op_proper : Proper (equiv ==> equiv ==> equiv) sg_op.
Axiom right_identity : forall x, equiv (sg_op x mon_unit) x.
Axiom left_inverse : forall x, equiv (sg_op (negate x) x) mon_unit.

#[global] Hint Rewrite @right_identity @left_inverse using apply _: group_cancellation.

(* Check that the rewrite hints are considered in the right order. *)

Goal equiv mon_unit (sg_op (negate mon_unit) mon_unit).
Proof.
rewrite_strat (try bottomup (hints group_cancellation)). (* should select left_inverse rather than right_identity *)
reflexivity.
Qed.
