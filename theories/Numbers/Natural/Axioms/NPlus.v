Require Export NAxioms.

Module Type NPlusSignature.
Declare Module Export NatModule : NatSignature.
Open Local Scope NatScope.

Parameter Inline plus : N -> N -> N.

Notation "x + y" := (plus x y) : NatScope.

Add Morphism plus with signature E ==> E ==> E as plus_wd.

Axiom plus_0_n : forall n, 0 + n == n.
Axiom plus_Sn_m : forall n m, (S n) + m == S (n + m).

End NPlusSignature.

Module NPlusProperties (Import NPlusModule : NPlusSignature).
Module Export NatPropertiesModule := NatProperties NatModule.
Open Local Scope NatScope.

Theorem plus_0_r : forall n, n + 0 == n.
Proof.
induct n.
now rewrite plus_0_n.
intros x IH.
rewrite plus_Sn_m.
now rewrite IH.
Qed.

Theorem plus_0_l : forall n, 0 + n == n.
Proof.
intro n.
now rewrite plus_0_n.
Qed.

Theorem plus_n_Sm : forall n m, n + S m == S (n + m).
Proof.
intros n m; generalize n; clear n. induct n.
now repeat rewrite plus_0_n.
intros x IH.
repeat rewrite plus_Sn_m; now rewrite IH.
Qed.

Theorem plus_Sn_m : forall n m, S n + m == S (n + m).
Proof.
intros.
now rewrite plus_Sn_m.
Qed.

Theorem plus_comm : forall n m, n + m == m + n.
Proof.
intros n m; generalize n; clear n. induct n.
rewrite plus_0_l; now rewrite plus_0_r.
intros x IH.
rewrite plus_Sn_m; rewrite plus_n_Sm; now rewrite IH.
Qed.

Theorem plus_assoc : forall n m p, n + (m + p) == (n + m) + p.
Proof.
intros n m p; generalize n; clear n. induct n.
now repeat rewrite plus_0_l.
intros x IH.
repeat rewrite plus_Sn_m; now rewrite IH.
Qed.

Theorem plus_shuffle1 : forall n m p q, (n + m) + (p + q) == (n + p) + (m + q).
Proof.
intros n m p q.
rewrite <- (plus_assoc n m (p + q)). rewrite (plus_comm m (p + q)).
rewrite <- (plus_assoc p q m). rewrite (plus_assoc n p (q + m)).
now rewrite (plus_comm q m).
Qed.

Theorem plus_shuffle2 : forall n m p q, (n + m) + (p + q) == (n + q) + (m + p).
Proof.
intros n m p q.
rewrite <- (plus_assoc n m (p + q)). rewrite (plus_assoc m p q).
rewrite (plus_comm (m + p) q). now rewrite <- (plus_assoc n q (m + p)).
Qed.

Theorem plus_1_l : forall n, 1 + n == S n.
Proof.
intro n; rewrite plus_Sn_m; now rewrite plus_0_n.
Qed.

Theorem plus_1_r : forall n, n + 1 == S n.
Proof.
intro n; rewrite plus_comm; apply plus_1_l.
Qed.

Theorem plus_cancel_l : forall n m p, p + n == p + m -> n == m.
Proof.
induct p.
do 2 rewrite plus_0_n; trivial.
intros p IH H. do 2 rewrite plus_Sn_m in H. apply S_inj in H. now apply IH.
Qed.

Theorem plus_cancel_r : forall n m p, n + p == m + p -> n == m.
Proof.
intros n m p.
rewrite plus_comm.
set (k := p + n); rewrite plus_comm; unfold k.
apply plus_cancel_l.
Qed.

Theorem plus_eq_0 : forall n m, n + m == 0 -> n == 0 /\ m == 0.
Proof.
intros n m; induct n.
rewrite plus_0_n; now split.
intros n IH H. rewrite plus_Sn_m in H.
absurd_hyp H; [|assumption]. unfold not; apply S_0.
Qed.

Theorem plus_eq_S :
  forall n m p, n + m == S p -> (exists n', n == S n') \/ (exists m', m == S m').
Proof.
intros n m p; nondep_induct n.
intro H; rewrite plus_0_l in H; right; now exists p.
intros n _; left; now exists n.
Qed.

Theorem succ_plus_discr : forall n m, m # S (n + m).
Proof.
intro n; induct m.
intro H. apply S_0 with (n := (n + 0)). now apply (proj2 (proj2 E_equiv)). (* symmetry *)
intros m IH H. apply S_inj in H. rewrite plus_n_Sm in H.
unfold not in IH; now apply IH.
Qed.

Theorem n_SSn : forall n, n # S (S n).
Proof.
intro n. pose proof (succ_plus_discr 1 n) as H.
rewrite plus_Sn_m in H; now rewrite plus_0_n in H.
Qed.

Theorem n_SSSn : forall n, n # S (S (S n)).
Proof.
intro n. pose proof (succ_plus_discr (S (S 0)) n) as H.
do 2 rewrite plus_Sn_m in H. now rewrite plus_0_n in H.
Qed.

Theorem n_SSSSn : forall n, n # S (S (S (S n))).
Proof.
intro n. pose proof (succ_plus_discr (S (S (S 0))) n) as H.
do 3 rewrite plus_Sn_m in H. now rewrite plus_0_n in H.
Qed.

(* The following section is devoted to defining a function that, given
two numbers whose some equals 1, decides which number equals 1. The
main property of the function is also proved .*)

(* First prove a theorem with ordinary disjunction *)
Theorem plus_eq_1 :
  forall m n, m + n == 1 ->  (m == 0 /\ n == 1) \/ (m == 1 /\ n == 0).
induct m.
intros n H; rewrite plus_0_n in H; left; now split.
intros n IH m H; rewrite plus_Sn_m in H; apply S_inj in H;
apply plus_eq_0 in H; destruct H as [H1 H2];
now right; split; [apply S_wd |].
Qed.

Definition plus_eq_1_dec (m n : N) : bool := recursion true (fun _ _ => false) m.

Theorem plus_eq_1_dec_step_wd : fun2_wd E eq_bool eq_bool (fun _ _ => false).
Proof.
unfold fun2_wd; intros. unfold eq_bool. reflexivity.
Qed.

Add Morphism plus_eq_1_dec with signature E ==> E ==> eq_bool as plus_eq_1_dec_wd.
Proof.
unfold fun2_wd, plus_eq_1_dec.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (EA := eq_bool).
unfold eq_bool; reflexivity.
unfold eq_fun2; unfold eq_bool; reflexivity.
assumption.
Qed.

Theorem plus_eq_1_dec_0 : forall n, plus_eq_1_dec 0 n = true.
Proof.
intro n. unfold plus_eq_1_dec.
now apply recursion_0.
Qed.

Theorem plus_eq_1_dec_S : forall m n, plus_eq_1_dec (S n) m = false.
Proof.
intros n m. unfold plus_eq_1_dec.
now rewrite (recursion_S eq_bool);
[| unfold eq_bool | apply plus_eq_1_dec_step_wd].
Qed.

Theorem plus_eq_1_dec_correct :
  forall m n, m + n == 1 ->
    (plus_eq_1_dec m n = true  -> m == 0 /\ n == 1) /\
    (plus_eq_1_dec m n = false -> m == 1 /\ n == 0).
Proof.
intros m n; induct m.
intro H. rewrite plus_0_l in H.
rewrite plus_eq_1_dec_0.
split; [intros; now split | intro H1; discriminate H1].
intros m _ H. rewrite plus_eq_1_dec_S.
split; [intro H1; discriminate | intros _ ].
rewrite plus_Sn_m in H. apply S_inj in H.
apply plus_eq_0 in H; split; [apply S_wd | ]; tauto.
Qed.

(* One could define n <= m := exists p, p + n == m. Then we have
dichotomy:

forall n m, n <= m \/ m <= n,

i.e.,

forall n m, (exists p, p + n == m) \/ (exists p, p + m == n)     (1)

We will need (1) in the proof of induction principle for integers
constructed as pairs of natural numbers. The formula (1) can be proved
using properties of order and truncated subtraction. Thus, p would be
m - n or n - m and (1) would hold by theorem minus_plus from Minus.v
depending on whether n <= m or m <= n. However, in proving induction
for integers constructed from natural numbers we do not need to
require implementations of order and minus; it is enough to prove (1)
here. *)

Theorem plus_dichotomy : forall n m, (exists p, p + n == m) \/ (exists p, p + m == n).
Proof.
intros n m; induct n.
left; exists m; apply plus_0_r.
intros n IH.
(* destruct IH as [p H | p H]. does not print a goal in ProofGeneral *)
destruct IH as [[p H] | [p H]].
destruct (O_or_S p) as [H1 | [p' H1]]; rewrite H1 in H.
rewrite plus_0_l in H. right; exists (S 0); rewrite H; rewrite plus_Sn_m; now rewrite plus_0_l.
left; exists p'; rewrite plus_n_Sm; now rewrite plus_Sn_m in H.
right; exists (S p). rewrite plus_Sn_m; now rewrite H.
Qed.

(* In proving the correctness of the definition of multiplication on
integers constructed from pairs of natural numbers, we'll need the
following fact about natural numbers:

a * x + u == a * y + v -> x + y' == x' + y -> a * x' + u = a * y' + v  (2)

Here x + y' == x' + y represents equality of integers (x, y) and
(x', y'), since a pair of natural numbers represents their integer
difference. On integers, the (2) could be proved by moving
a * y to the left, factoring out a and replacing x - y by x' - y'.
However, the whole point is that we are only in the process of
constructing integers, so this has to be proved for natural numbers,
where we cannot move terms from one side of an equation to the other.
We first prove the special case of (2) where a == 1. *)

Theorem plus_repl_pair : forall n m n' m' u v,
  n + u == m + v -> n + m' == n' + m -> n' + u == m' + v.
Proof.
induct n.
intros m n' m' u v H1 H2. rewrite plus_0_l in H1. rewrite plus_0_l in H2.
rewrite H1; rewrite H2. now rewrite plus_assoc.
intros n IH m n' m' u v H1 H2. rewrite plus_Sn_m in H1. rewrite plus_Sn_m in H2.
assert (H : (exists m'', m == S m'') \/ ((exists v', v == S v') /\ (exists n'', n' == S n''))).
symmetry in H1; symmetry in H2;
destruct (plus_eq_S m v (n + u) H1); destruct (plus_eq_S n' m (n + m') H2).
now left. now left. right; now split. now left.
(* destruct H as [[m'' H] | [v' H3] [n'' H4]]. *)
(* The command above produces a warning and the PG does not show a goal !!! *) 
destruct H as [[m'' H] | [[v' H3] [n'' H4]]].
rewrite H in H1, H2. rewrite plus_Sn_m in H1; rewrite plus_n_Sm in H2.
apply S_inj in H1; apply S_inj in H2. now apply (IH m'').
rewrite H3; rewrite H4; rewrite plus_Sn_m; rewrite plus_n_Sm; apply S_wd.
rewrite H3 in H1; rewrite H4 in H2; rewrite plus_Sn_m in H2; rewrite plus_n_Sm in H1;
apply S_inj in H1; apply S_inj in H2. now apply (IH m).
Qed.

(* The formula (2) will be proved in NTimes.v *)

End NPlusProperties.
