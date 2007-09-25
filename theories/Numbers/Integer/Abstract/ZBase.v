Require Export ZAxioms.
Require Import NZTimesOrder.

Module ZBasePropFunct (Import ZAxiomsMod : ZAxiomsSig).
Open Local Scope NatIntScope.

Module Export NZTimesOrderMod := NZTimesOrderPropFunct NZOrdAxiomsMod.

Theorem Zneq_symm : forall n m : Z, n ~= m -> m ~= n.
Proof NZneq_symm.

Theorem Zsucc_inj : forall n1 n2 : Z, S n1 == S n2 -> n1 == n2.
Proof NZsucc_inj.

Theorem Zsucc_inj_wd : forall n1 n2 : Z, S n1 == S n2 <-> n1 == n2.
Proof NZsucc_inj_wd.

Theorem Zsucc_inj_wd_neg : forall n m : Z, S n ~= S m <-> n ~= m.
Proof NZsucc_inj_wd_neg.

Theorem Zcentral_induction :
forall A : Z -> Prop, predicate_wd E A ->
  forall z : Z, A z ->
    (forall n : Z, A n <-> A (S n)) ->
      forall n : Z, A n.
Proof NZcentral_induction.

End ZBasePropFunct.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
