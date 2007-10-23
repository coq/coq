Require Export NAxioms.
Require Import NZTimesOrder. (* The last property functor on NZ, which subsumes all others *)

Module NBasePropFunct (Export NAxiomsMod : NAxiomsSig).

Open Local Scope NatScope.

(* We call the last property functor on NZ, which includes all the previous
ones, to get all properties of NZ at once. This way we will include them
only one time. *)

Module Export NZTimesOrderMod := NZTimesOrderPropFunct NZOrdAxiomsMod.

(* Here we probably need to re-prove all axioms declared in NAxioms.v to
make sure that the definitions like N, S and plus are unfolded in them,
since unfolding is done only inside a functor. In fact, we'll do it in the
files that prove the corresponding properties. In those files, we will also
rename properties proved in NZ files by removing NZ from their names. In
this way, one only has to consult, for example, NPlus.v to see all
available properties for plus, i.e., one does not have to go to NAxioms.v
for axioms and NZPlus.v for theorems. *)

Theorem succ_wd : forall n1 n2 : N, n1 == n2 -> S n1 == S n2.
Proof NZsucc_wd.

Theorem pred_wd : forall n1 n2 : N, n1 == n2 -> P n1 == P n2.
Proof NZpred_wd.

Theorem pred_succ : forall n : N, P (S n) == n.
Proof NZpred_succ.

Theorem pred_0 : P 0 == 0.
Proof pred_0.

Theorem neq_symm : forall n m : N, n ~= m -> m ~= n.
Proof NZneq_symm.

Theorem succ_inj : forall n1 n2 : N, S n1 == S n2 -> n1 == n2.
Proof NZsucc_inj.

Theorem succ_inj_wd : forall n1 n2 : N, S n1 == S n2 <-> n1 == n2.
Proof NZsucc_inj_wd.

Theorem succ_inj_wd_neg : forall n m : N, S n ~= S m <-> n ~= m.
Proof NZsucc_inj_wd_neg.

(* Decidability of equality was proved only in NZOrder, but since it
does not mention order, we'll put it here *)

Theorem eq_em : forall n m : N, n == m \/ n ~= m.
Proof NZeq_em.

(* Now we prove that the successor of a number is not zero by defining a
function (by recursion) that maps 0 to false and the successor to true *)

Definition if_zero (A : Set) (a b : A) (n : N) : A :=
  recursion a (fun _ _ => b) n.

Add Morphism if_zero with signature @eq ==> @eq ==> Neq ==> @eq as if_zero_wd.
Proof.
intros; unfold if_zero. apply recursion_wd with (Aeq := (@eq A)).
reflexivity. unfold eq_fun2; now intros. assumption.
Qed.

Theorem if_zero_0 : forall (A : Set) (a b : A), if_zero A a b 0 = a.
Proof.
unfold if_zero; intros; now rewrite recursion_0.
Qed.

Theorem if_zero_succ : forall (A : Set) (a b : A) (n : N), if_zero A a b (S n) = b.
Proof.
intros; unfold if_zero.
now rewrite (@recursion_succ A (@eq A)); [| | unfold fun2_wd; now intros].
Qed.

Implicit Arguments if_zero [A].

Theorem neq_succ_0 : forall n : N, ~ S n == 0.
Proof.
intros n H.
assert (true = false); [| discriminate].
replace true with (if_zero false true (S n)) by apply if_zero_succ.
pattern false at 2; replace false with (if_zero false true 0) by apply if_zero_0.
now rewrite H.
Qed.

(* Next, we show that all numbers are nonnegative and recover regular induction
from the bidirectional induction on NZ *)

Theorem le_0_l : forall n : N, 0 <= n.
Proof.
NZinduct n.
le_equal.
intro n; split.
apply NZle_le_succ.
intro H; apply -> NZle_succ_le_or_eq_succ in H; destruct H as [H | H].
assumption.
symmetry in H; false_hyp H neq_succ_0.
Qed.

Theorem induction :
  forall A : N -> Prop, predicate_wd Neq A ->
    A 0 -> (forall n : N, A n -> A (S n)) -> forall n : N, A n.
Proof.
intros A A_wd A0 AS n; apply NZright_induction with 0; try assumption.
intros; auto; apply le_0_l. apply le_0_l.
Qed.

(* The theorems NZinduction, NZcentral_induction and the tactic NZinduct
refer to bidirectional induction, which is not useful on natural
numbers. Therefore, we define a new induction tactic for natural numbers.
We do not have to call "Declare Left Step" and "Declare Right Step"
commands again, since the data for stepl and stepr tactics is inherited
from N. *)

Ltac induct n := induction_maker n ltac:(apply induction).

Theorem case_analysis :
  forall A : N -> Prop, predicate_wd Neq A ->
    A 0 -> (forall n : N, A (S n)) -> forall n : N, A n.
Proof.
intros; apply induction; auto.
Qed.

Ltac cases n := induction_maker n ltac:(apply case_analysis).

Theorem neq_0 : ~ forall n, n == 0.
Proof.
intro H; apply (neq_succ_0 0). apply H.
Qed.

Theorem neq_0_succ : forall n, n ~= 0 <-> exists m, n == S m.
Proof.
cases n. split; intro H;
[now elim H | destruct H as [m H]; symmetry in H; false_hyp H neq_succ_0].
intro n; split; intro H; [now exists n | apply neq_succ_0].
Qed.

Theorem zero_or_succ : forall n, n == 0 \/ exists m, n == S m.
Proof.
cases n.
now left.
intro n; right; now exists n.
Qed.

Theorem eq_pred_0 : forall n : N, P n == 0 <-> n == 0 \/ n == 1.
Proof.
cases n.
rewrite pred_0. setoid_replace (0 == 1) with False using relation iff. tauto.
split; intro H; [symmetry in H; false_hyp H neq_succ_0 | elim H].
intro n. rewrite pred_succ. rewrite_false (S n == 0) neq_succ_0.
rewrite succ_inj_wd. tauto.
Qed.

Theorem succ_pred : forall n : N, n ~= 0 -> S (P n) == n.
Proof.
cases n.
intro H; elimtype False; now apply H.
intros; now rewrite pred_succ.
Qed.

Theorem pred_inj : forall n m : N, n ~= 0 -> m ~= 0 -> P n == P m -> n == m.
Proof.
intros n m; cases n.
intros H; elimtype False; now apply H.
intros n _; cases m.
intros H; elimtype False; now apply H.
intros m H2 H3. do 2 rewrite pred_succ in H3. now rewrite H3.
Qed.

(* The following induction principle is useful for reasoning about, e.g.,
Fibonacci numbers *)

Section PairInduction.

Variable A : N -> Prop.
Hypothesis A_wd : predicate_wd Neq A.

Add Morphism A with signature Neq ==> iff as A_morph.
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

(*Ltac pair_induct n := induction_maker n ltac:(apply pair_induction).*)

(* The following is useful for reasoning about, e.g., Ackermann function *)
Section TwoDimensionalInduction.

Variable R : N -> N -> Prop.
Hypothesis R_wd : rel_wd Neq Neq R.

Add Morphism R with signature Neq ==> Neq ==> iff as R_morph.
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

(*Ltac two_dim_induct n m :=
  try intros until n;
  try intros until m;
  pattern n, m; apply two_dim_induction; clear n m;
  [solve_rel_wd | | | ].*)

Section DoubleInduction.

Variable R : N -> N -> Prop.
Hypothesis R_wd : rel_wd Neq Neq R.

Add Morphism R with signature Neq ==> Neq ==> iff as R_morph1.
Proof.
exact R_wd.
Qed.

Theorem double_induction :
   (forall m : N, R 0 m) ->
   (forall n : N, R (S n) 0) ->
   (forall n m : N, R n m -> R (S n) (S m)) -> forall n m : N, R n m.
Proof.
intros H1 H2 H3; induct n; auto.
intros n H; cases m; auto.
Qed.

End DoubleInduction.

Ltac double_induct n m :=
  try intros until n;
  try intros until m;
  pattern n, m; apply double_induction; clear n m;
  [solve_rel_wd | | | ].

End NBasePropFunct.

