Require Export NAxioms.

Module Type NPlusSignature.
Declare Module Export NatModule : NatSignature.
Open Local Scope NatScope.

Parameter (*Inline*) plus : N -> N -> N.

Notation "x + y" := (plus x y) : NatScope.

Add Morphism plus with signature E ==> E ==> E as plus_wd.

Axiom plus_0_l : forall n, 0 + n == n.
Axiom plus_S_l : forall n m, (S n) + m == S (n + m).

End NPlusSignature.

Module NPlusProperties
  (NatMod : NatSignature)
  (Import NPlusModule : NPlusSignature with Module NatModule := NatMod).
Module Export NatPropertiesModule := NatProperties NatModule.
Import NatMod.
Open Local Scope NatScope.

(* If H1 : t1 == u1 and H2 : t2 == u2 then "add_equations H1 H2 as H3"
adds the hypothesis H3 : t1 + t2 == u1 + u2 *)
Tactic Notation "add_equations" constr(H1) constr(H2) "as" ident(H3) :=
match (type of H1) with
| ?t1 == ?u1 => match (type of H2) with
              | ?t2 == ?u2 => pose proof (plus_wd t1 u1 H1 t2 u2 H2) as H3
              | _ => fail 2 ":" H2 "is not an equation"
              end
| _ => fail 1 ":" H1 "is not an equation"
end.

Theorem plus_0_r : forall n, n + 0 == n.
Proof.
induct n.
now rewrite plus_0_l.
intros x IH.
rewrite plus_S_l.
now rewrite IH.
Qed.

Theorem plus_S_r : forall n m, n + S m == S (n + m).
Proof.
intros n m; generalize n; clear n. induct n.
now repeat rewrite plus_0_l.
intros x IH.
repeat rewrite plus_S_l; now rewrite IH.
Qed.

Theorem plus_S_l : forall n m, S n + m == S (n + m).
Proof.
intros.
now rewrite plus_S_l.
Qed.

Theorem plus_comm : forall n m, n + m == m + n.
Proof.
intros n m; generalize n; clear n. induct n.
rewrite plus_0_l; now rewrite plus_0_r.
intros x IH.
rewrite plus_S_l; rewrite plus_S_r; now rewrite IH.
Qed.

Theorem plus_assoc : forall n m p, n + (m + p) == (n + m) + p.
Proof.
intros n m p; generalize n; clear n. induct n.
now repeat rewrite plus_0_l.
intros x IH.
repeat rewrite plus_S_l; now rewrite IH.
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
intro n; rewrite plus_S_l; now rewrite plus_0_l.
Qed.

Theorem plus_1_r : forall n, n + 1 == S n.
Proof.
intro n; rewrite plus_comm; apply plus_1_l.
Qed.

Theorem plus_cancel_l : forall n m p, p + n == p + m -> n == m.
Proof.
induct p.
do 2 rewrite plus_0_l; trivial.
intros p IH H. do 2 rewrite plus_S_l in H. apply S_inj in H. now apply IH.
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
rewrite plus_0_l; now split.
intros n IH H. rewrite plus_S_l in H.
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
intros m IH H. apply S_inj in H. rewrite plus_S_r in H.
unfold not in IH; now apply IH.
Qed.

(* The following section is devoted to defining a function that, given
two numbers whose some equals 1, decides which number equals 1. The
main property of the function is also proved .*)

(* First prove a theorem with ordinary disjunction *)
Theorem plus_eq_1 :
  forall m n, m + n == 1 ->  (m == 0 /\ n == 1) \/ (m == 1 /\ n == 0).
induct m.
intros n H; rewrite plus_0_l in H; left; now split.
intros n IH m H; rewrite plus_S_l in H; apply S_inj in H;
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
rewrite plus_S_l in H. apply S_inj in H.
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
rewrite plus_0_l in H. right; exists (S 0); rewrite H; rewrite plus_S_l; now rewrite plus_0_l.
left; exists p'; rewrite plus_S_r; now rewrite plus_S_l in H.
right; exists (S p). rewrite plus_S_l; now rewrite H.
Qed.

End NPlusProperties.
