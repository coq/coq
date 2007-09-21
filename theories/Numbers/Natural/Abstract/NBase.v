Require Export NAxioms.
Require Import NZTimesOrder. (* The last property functor on NZ, which subsumes all others *)

Module NBasePropFunct (Import NAxiomsMod : NAxiomsSig).
Open Local Scope NatScope.

(* We call the last property functor on NZ, which includes all the previous
ones, to get all properties of NZ at once. This way we will include them
only one time. *)

Module NZOrdAxiomsMod := NNZFunct NAxiomsMod.
Module Export NZTimesOrderMod := NZTimesOrderPropFunct NZOrdAxiomsMod.

(* Here we probably need to re-prove all axioms declared in NAxioms.v to
make sure that the definitions like N, S and plus are unfolded in them,
since unfolding is done only inside a functor. In fact, we'll do it in the
files that prove the corresponding properties. In those files, we will also
rename properties proved in NZ files by removing NZ from their names. In
this way, one only has to consult, for example, NPlus.v to see all
available properties for plus (i.e., one does not have to go to NAxioms.v
and NZPlus.v). *)

Theorem E_equiv : equiv N E.
Proof E_equiv.

Theorem induction :
  forall A : N -> Prop, predicate_wd E A ->
    A 0 -> (forall n : N, A n -> A (S n)) -> forall n : N, A n.
Proof induction.

Theorem pred_0 : P 0 == 0.
Proof pred_0.

Theorem pred_succ : forall n : N, P (S n) == n.
Proof pred_succ.

Theorem neq_symm : forall n m : N, n ~= m -> m ~= n.
Proof NZneq_symm.

Theorem succ_inj : forall n1 n2 : N, S n1 == S n2 -> n1 == n2.
Proof NZsucc_inj.

Theorem succ_inj_wd : forall n1 n2 : N, S n1 == S n2 <-> n1 == n2.
Proof NZsucc_inj_wd.

Theorem succ_inj_wd_neg : forall n m : N, S n ~= S m <-> n ~= m.
Proof NZsucc_inj_wd_neg.

(* The theorems NZinduction, NZcentral_induction and the tactic NZinduct
refer to bidirectional induction, which is not so useful on natural
numbers. Therefore, we define a new induction tactic for natural numbers.
We do not have to call "Declare Left Step" and "Declare Right Step"
commands again, since the data for stepl and stepr tactics is inherited
from NZ. *)

Tactic Notation "induct" ident(n) := induction_maker n ltac:(apply induction).
(* FIXME: "Ltac induct n := induction_maker n ltac:(apply induction)" does not work (bug 1703) *)

(* Now we add properties peculiar to natural numbers *)

Theorem nondep_induction :
  forall A : N -> Prop, predicate_wd E A ->
    A 0 -> (forall n : N, A (S n)) -> forall n : N, A n.
Proof.
intros; apply induction; auto.
Qed.

Tactic Notation "nondep_induct" ident(n) :=
  induction_maker n ltac:(apply nondep_induction).

(* The fact "forall n : N, S n ~= 0" can be proved either by building a
function (using recursion) that maps 0 ans S n to two provably different
terms, or from the axioms of order *)

Theorem neq_succ_0 : forall n : N, S n ~= 0.
Proof.
intros n H. apply nlt_0_r with n. rewrite <- H.
apply <- lt_succ_le. apply <- le_lt_or_eq. now right.
Qed.

Theorem neq_0 : ~ forall n, n == 0.
Proof.
intro H; apply (neq_succ_0 0). apply H.
Qed.

Theorem neq_0_succ : forall n, n ~= 0 <-> exists m, n == S m.
Proof.
nondep_induct n. split; intro H;
[now elim H | destruct H as [m H]; symmetry in H; false_hyp H neq_succ_0].
intro n; split; intro H; [now exists n | apply neq_succ_0].
Qed.

Theorem zero_or_succ : forall n, n == 0 \/ exists m, n == S m.
Proof.
nondep_induct n; [now left | intros n; right; now exists n].
Qed.

Theorem eq_pred_0 : forall n : N, P n == 0 <-> n == 0 \/ n == 1.
Proof.
nondep_induct n.
rewrite pred_0. setoid_replace (0 == 1) with False using relation iff. tauto.
split; intro H; [symmetry in H; false_hyp H neq_succ_0 | elim H].
intro n. rewrite pred_succ. rewrite_false (S n == 0) neq_succ_0.
rewrite succ_inj_wd. tauto.
Qed.

Theorem succ_pred : forall n : N, n ~= 0 -> S (P n) == n.
Proof.
nondep_induct n.
intro H; elimtype False; now apply H.
intros; now rewrite pred_succ.
Qed.

Theorem pred_inj : forall n m : N, n ~= 0 -> m ~= 0 -> P n == P m -> n == m.
Proof.
intros n m; nondep_induct n.
intros H; elimtype False; now apply H.
intros n H1; nondep_induct m.
intros H; elimtype False; now apply H.
intros m H2 H3. do 2 rewrite pred_succ in H3. now apply succ_wd.
Qed.

(* The following induction principle is useful for reasoning about, e.g.,
Fibonacci numbers *)

Section PairInduction.

Variable A : N -> Prop.
Hypothesis A_wd : predicate_wd E A.

Add Morphism A with signature E ==> iff as A_morph.
Proof.
exact A_wd.
Qed.

Theorem pair_induction :
  A 0 -> A 1 ->
    (forall n, A n -> A (S n) -> A (S (S n))) -> forall n, A n.
Proof.
intros until 3.
assert (D : forall n, A n /\ A (S n)); [ |intro n; exact (proj1 (D n))].
induct n; [ | intros n [IH1 IH2]]; auto.
Qed.

End PairInduction.

Tactic Notation "pair_induct" ident(n) := induction_maker n ltac:(apply pair_induction).

(* The following is useful for reasoning about, e.g., Ackermann function *)
Section TwoDimensionalInduction.

Variable R : N -> N -> Prop.
Hypothesis R_wd : rel_wd E E R.

Add Morphism R with signature E ==> E ==> iff as R_morph.
Proof.
exact R_wd.
Qed.

Theorem two_dim_induction :
   R 0 0 ->
   (forall n m, R n m -> R n (S m)) ->
   (forall n, (forall m, R n m) -> R (S n) 0) -> forall n m, R n m.
Proof.
intros H1 H2 H3. induct n.
induct m.
exact H1. exact (H2 0).
intros n IH. induct m.
now apply H3. exact (H2 (S n)).
Qed.

End TwoDimensionalInduction.

Tactic Notation "two_dim_induct" ident(n) ident(m) :=
  try intros until n;
  try intros until m;
  pattern n, m; apply two_dim_induction; clear n m;
  [solve_rel_wd | | | ].

Section DoubleInduction.

Variable R : N -> N -> Prop.
Hypothesis R_wd : rel_wd E E R.

Add Morphism R with signature E ==> E ==> iff as R_morph1.
Proof.
exact R_wd.
Qed.

Theorem double_induction :
   (forall m : N, R 0 m) ->
   (forall n : N, R (S n) 0) ->
   (forall n m : N, R n m -> R (S n) (S m)) -> forall n m : N, R n m.
Proof.
intros H1 H2 H3; induct n; auto.
intros n IH; nondep_induct m; auto.
Qed.

End DoubleInduction.

Tactic Notation "double_induct" ident(n) ident(m) :=
  try intros until n;
  try intros until m;
  pattern n, m; apply double_induction; clear n m;
  [solve_rel_wd | | | ].

End NBasePropFunct.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
