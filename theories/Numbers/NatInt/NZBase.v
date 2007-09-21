Require Import NZAxioms.

Module NZBasePropFunct (Import NZAxiomsMod : NZAxiomsSig).
Open Local Scope NatIntScope.

Theorem NZneq_symm : forall n m : NZ, n ~= m -> m ~= n.
Proof.
intros n m H1 H2; symmetry in H2; false_hyp H2 H1.
Qed.

Theorem NZE_stepl : forall x y z : NZ, x == y -> x == z -> z == y.
Proof.
intros x y z H1 H2; now rewrite <- H1.
Qed.

Declare Left Step NZE_stepl.
(* The right step lemma is just the transitivity of NZE *)
Declare Right Step (proj1 (proj2 NZE_equiv)).

Theorem NZsucc_inj : forall n1 n2 : NZ, S n1 == S n2 -> n1 == n2.
Proof.
intros n1 n2 H.
apply NZpred_wd in H. now do 2 rewrite NZpred_succ in H.
Qed.

(* The following theorem is useful as an equivalence for proving
bidirectional induction steps *)
Theorem NZsucc_inj_wd : forall n1 n2 : NZ, S n1 == S n2 <-> n1 == n2.
Proof.
intros; split.
apply NZsucc_inj.
apply NZsucc_wd.
Qed.

Theorem NZsucc_inj_wd_neg : forall n m : NZ, S n ~= S m <-> n ~= m.
Proof.
intros; now rewrite NZsucc_inj_wd.
Qed.

(* We cannot prove that the predecessor is injective, nor that it is
left-inverse to the successor at this point *)

Section CentralInduction.

Variable A : NZ -> Prop.
(* FIXME: declaring "A : predicate NZ" leads to the error during the
declaration of the morphism below because the "predicate NZ" is not
recognized as a type of function. Maybe it should do "eval hnf" or
something like this. The same goes for "relation". *)

Hypothesis A_wd : predicate_wd NZE A.

Add Morphism A with signature NZE ==> iff as A_morph.
Proof A_wd.

Theorem NZcentral_induction :
  forall z : NZ, A z ->
    (forall n : NZ, A n <-> A (S n)) ->
      forall n : NZ, A n.
Proof.
intros z Base Step; revert Base; pattern z; apply NZinduction.
solve_predicate_wd.
intro; now apply NZinduction.
intro; pose proof (Step n); tauto.
Qed.

End CentralInduction.

Tactic Notation "NZinduct" ident(n) :=
  induction_maker n ltac:(apply NZinduction).

Tactic Notation "NZinduct" ident(n) constr(z) :=
  induction_maker n ltac:(apply NZcentral_induction with (z := z)).

End NZBasePropFunct.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)

