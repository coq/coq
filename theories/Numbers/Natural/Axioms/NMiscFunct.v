Require Import Bool. (* To get the orb and negb function *)
Require Export NStrongRec.
Require Export NTimesOrder.

Module MiscFunctFunctor (Import NatMod : NatSignature).
Module Export StrongRecPropertiesModule := StrongRecProperties NatMod.
Open Local Scope NatScope.

(*****************************************************)
(**                   Addition                       *)

Definition plus (x y : N) := recursion y (fun _ p => S p) x.

Lemma plus_step_wd : fun2_wd E E E (fun _ p => S p).
Proof.
unfold fun2_wd; intros _ _ _ p p' H; now rewrite H.
Qed.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
unfold plus.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (EA := E).
assumption.
unfold eq_fun2; intros _ _ _ p p' Epp'; now rewrite Epp'.
assumption.
Qed.

Theorem plus_0 : forall y, plus 0 y == y.
Proof.
intro y. unfold plus.
(*pose proof (recursion_0 E y (fun _ p => S p)) as H.*)
rewrite recursion_0. apply (proj1 E_equiv).
Qed.

Theorem plus_S : forall x y, plus (S x) y == S (plus x y).
Proof.
intros x y; unfold plus.
now rewrite (recursion_S E); [|apply plus_step_wd|].
Qed.

(*****************************************************)
(**                  Multiplication                  *)

Definition times (x y : N) := recursion 0 (fun x p => plus y p) x.

Lemma times_step_wd : forall y, fun2_wd E E E (fun x p => plus y p).
Proof.
unfold fun2_wd. intros y _ _ _ p p' Ezz'.
now apply plus_wd.
Qed.

Lemma times_step_equal :
  forall y y', y == y' -> eq_fun2 E E E (fun x p => plus y p) (fun x p => plus y' p).
Proof.
unfold eq_fun2; intros; apply plus_wd; assumption.
Qed.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
unfold times.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (EA := E).
reflexivity. apply times_step_equal. assumption. assumption.
Qed.

Theorem times_0 : forall y, times 0 y == 0.
Proof.
intro y. unfold times. now rewrite recursion_0.
Qed.

Theorem times_S : forall x y, times (S x) y == plus y (times x y).
Proof.
intros x y; unfold times.
now rewrite (recursion_S E); [| apply times_step_wd |].
Qed.

(*****************************************************)
(**                   Less Than                      *)

Definition lt (m : N) : N -> bool :=
  recursion (if_zero false true)
            (fun _ f => fun n => recursion false (fun n' _ => f n') n)
            m.

(* It would be more efficient to make a three-way comparison, i.e.,
return Eq, Lt, or Gt, but since these are no-use default functions,
we define <= as (< or =) *)
Definition le (n m : N) := lt n m || e n m.

Theorem le_lt : forall n m, le n m <-> lt n m \/ n == m.
Proof.
intros n m. rewrite E_equiv_e. unfold le.
do 3 rewrite eq_true_unfold.
assert (H : lt n m || e n m = true <-> lt n m = true \/ e n m = true).
split; [apply orb_prop | apply orb_true_intro].
now rewrite H.
Qed.

Theorem le_intro_left : forall n m, lt n m -> le n m.
Proof.
intros; rewrite le_lt; now left.
Qed.

Theorem le_intro_right : forall n m, n == m -> le n m.
Proof.
intros; rewrite le_lt; now right.
Qed.

Lemma lt_base_wd : eq_fun E eq_bool (if_zero false true) (if_zero false true).
unfold eq_fun, eq_bool; intros; apply if_zero_wd; now unfold LE_Set.
Qed.

Lemma lt_step_wd :
  let step := (fun _ f => fun n => recursion false (fun n' _ => f n') n) in
    eq_fun2 E (eq_fun E eq_bool) (eq_fun E eq_bool) step step.
Proof.
unfold eq_fun2, eq_fun, eq_bool.
intros x x' Exx' f f' Eff' y y' Eyy'.
apply recursion_wd with (EA := eq_bool); unfold eq_bool.
reflexivity.
unfold eq_fun2; intros; now apply Eff'.
assumption.
Qed.

Lemma lt_curry_wd : forall m m', m == m' -> eq_fun E eq_bool (lt m) (lt m').
Proof.
unfold lt.
intros m m' Emm'.
apply recursion_wd with (EA := eq_fun E eq_bool).
apply lt_base_wd.
apply lt_step_wd.
assumption.
Qed.

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
unfold eq_fun; intros m m' Emm' n n' Enn'.
now apply lt_curry_wd.
Qed.

(* Note that if we unfold lt along with eq_fun above, then "apply" signals
as error "Impossible to unify", not just, e.g., "Cannot solve second-order
unification problem". Something is probably wrong. *)

Add Morphism le with signature E ==> E ==> eq_bool as le_wd.
Proof.
intros x1 x2 H1 x3 x4 H2; unfold le; rewrite H1; now rewrite H2.
Qed.

Theorem lt_base_eq : forall n, lt 0 n = if_zero false true n.
Proof.
intro n; unfold lt; now rewrite recursion_0.
Qed.

Theorem lt_step_eq : forall m n, lt (S m) n = recursion false (fun n' _ => lt m n') n.
Proof.
intros m n; unfold lt.
pose proof (recursion_S (eq_fun E eq_bool) (if_zero false true)
  (fun _ f => fun n => recursion false (fun n' _ => f n') n)
  lt_base_wd lt_step_wd m n n) as H.
unfold eq_bool in H.
assert (H1 : n == n); [reflexivity | apply H in H1; now rewrite H1].
Qed.

Theorem lt_0 : forall n, ~ lt n 0.
Proof.
nondep_induct n.
rewrite lt_base_eq; rewrite if_zero_0; now intro.
intros n; rewrite lt_step_eq. rewrite recursion_0. now intro.
Qed.

(* Above, we rewrite applications of function. Is it possible to rewrite
functions themselves, i.e., rewrite (recursion lt_base lt_step (S n)) to
lt_step n (recursion lt_base lt_step n)? *)

Lemma lt_0_1 : lt 0 1.
Proof.
rewrite lt_base_eq; now rewrite if_zero_S.
Qed.

Lemma lt_0_Sn : forall n, lt 0 (S n).
Proof.
intro n; rewrite lt_base_eq; now rewrite if_zero_S.
Qed.

Lemma lt_Sn_Sm : forall n m, lt (S n) (S m) <-> lt n m.
Proof.
intros n m.
rewrite lt_step_eq. rewrite (recursion_S eq_bool).
reflexivity.
now unfold eq_bool.
unfold fun2_wd; intros; now apply lt_wd.
Qed.

Theorem lt_S : forall m n, lt m (S n) <-> le m n.
Proof.
assert (A : forall m n, lt m (S n) <-> lt m n \/ m == n).
induct m.
nondep_induct n;
[split; intro; [now right | apply lt_0_1] |
intro n; split; intro; [left |]; apply lt_0_Sn].
intros n IH. nondep_induct n0.
split.
intro. assert (H1 : lt n 0); [now apply -> lt_Sn_Sm | false_hyp H1 lt_0].
intro H; destruct H as [H | H].
false_hyp H lt_0. false_hyp H S_0.
intro m. pose proof (IH m) as H; clear IH.
assert (lt (S n) (S (S m)) <-> lt n (S m)); [apply lt_Sn_Sm |].
assert (lt (S n) (S m) <-> lt n m); [apply lt_Sn_Sm |].
assert (S n == S m <-> n == m); [split; [ apply S_inj | apply S_wd]|]. tauto.
intros; rewrite le_lt; apply A.
Qed.

(*****************************************************)
(**                     Even                         *)

Definition even (x : N) := recursion true (fun _ p => negb p) x.

Lemma even_step_wd : fun2_wd E eq_bool eq_bool (fun x p => if p then false else true).
Proof.
unfold fun2_wd.
intros x x' Exx' b b' Ebb'.
unfold eq_bool; destruct b; destruct b'; now simpl.
Qed.

Add Morphism even with signature E ==> eq_bool as even_wd.
Proof.
unfold even; intros.
apply recursion_wd with (A := bool) (EA := eq_bool).
now unfold eq_bool.
unfold eq_fun2. intros _ _ _ b b' Ebb'. unfold eq_bool; destruct b; destruct b'; now simpl.
assumption.
Qed.

Theorem even_0 : even 0 = true.
Proof.
unfold even.
now rewrite recursion_0.
Qed.

Theorem even_S : forall x : N, even (S x) = negb (even x).
Proof.
unfold even.
intro x; rewrite (recursion_S (@eq bool)); try reflexivity.
unfold fun2_wd.
intros _ _ _ b b' Ebb'. destruct b; destruct b'; now simpl.
Qed.

(*****************************************************)
(**                Division by 2                     *)

Definition half_aux (x : N) : N * N :=
  recursion (0, 0) (fun _ p => let (x1, x2) := p in ((S x2, x1))) x.

Definition half (x : N) := snd (half_aux x).

Definition E2 := prod_rel E E.

Add Relation (prod N N) E2
reflexivity proved by (prod_rel_refl N N E E E_equiv E_equiv)
symmetry proved by (prod_rel_symm N N E E E_equiv E_equiv)
transitivity proved by (prod_rel_trans N N E E E_equiv E_equiv)
as E2_rel.

Lemma half_step_wd: fun2_wd E E2 E2 (fun _ p => let (x1, x2) := p in ((S x2, x1))).
Proof.
unfold fun2_wd, E2, prod_rel.
intros _ _ _ p1 p2 [H1 H2].
destruct p1; destruct p2; simpl in *.
now split; [rewrite H2 |].
Qed.

Add Morphism half with signature E ==> E as half_wd.
Proof.
unfold half.
assert (H: forall x y, x == y -> E2 (half_aux x) (half_aux y)).
intros x y Exy; unfold half_aux; apply recursion_wd with (EA := E2); unfold E2.
unfold E2.
unfold prod_rel; simpl; now split.
unfold eq_fun2, prod_rel; simpl.
intros _ _ _ p1 p2; destruct p1; destruct p2; simpl.
intros [H1 H2]; split; [rewrite H2 | assumption]. reflexivity. assumption.
unfold E2, prod_rel in H. intros x y Exy; apply H in Exy.
exact (proj2 Exy).
Qed.

(*****************************************************)
(**            Logarithm for the base 2              *)

Definition log (x : N) : N :=
strong_rec 0
           (fun x g =>
              if (e x 0) then 0
              else if (e x 1) then 0
              else S (g (half x)))
           x.

Add Morphism log with signature E ==> E as log_wd.
Proof.
intros x x' Exx'. unfold log.
apply strong_rec_wd with (EA := E); try (reflexivity || assumption).
unfold eq_fun2. intros y y' Eyy' g g' Egg'.
assert (H : e y 0 = e y' 0); [now apply e_wd|].
rewrite <- H; clear H.
assert (H : e y 1 = e y' 1); [now apply e_wd|].
rewrite <- H; clear H.
assert (H : S (g (half y)) == S (g' (half y')));
[apply S_wd; apply Egg'; now apply half_wd|].
now destruct (e y 0); destruct (e y 1).
Qed.

(*********************************************************)
(** To get the properties of plus, times and lt defined  *)
(** via recursion, we form the corresponding modules and *)
(** apply the properties functors to these modules       *)

Module NDefaultPlusModule <: NPlusSignature.

Module NatModule := NatMod.
(* If we used the name NatModule instead of NatMod then this would
produce many warnings like "Trying to mask the absolute name
NatModule", "Trying to mask the absolute name Nat.O" etc. *)

Definition plus := plus.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
exact plus_wd.
Qed.

Theorem plus_0_n : forall n, plus 0 n == n.
Proof.
exact plus_0.
Qed.

Theorem plus_Sn_m : forall n m, plus (S n) m == S (plus n m).
Proof.
exact plus_S.
Qed.

End NDefaultPlusModule.

Module NDefaultTimesModule <: NTimesSignature.
Module NPlusModule := NDefaultPlusModule.

Definition times := times.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
exact times_wd.
Qed.

Theorem times_0_n : forall n, times 0 n == 0.
Proof.
exact times_0.
Qed.

Theorem times_Sn_m : forall n m, times (S n) m == plus m (times n m).
Proof.
exact times_S.
Qed.

End NDefaultTimesModule.

Module NDefaultOrderModule <: NOrderSignature.
Module NatModule := NatMod.

Definition lt := lt.
Definition le := le.

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
exact lt_wd.
Qed.

Add Morphism le with signature E ==> E ==> eq_bool as le_wd.
Proof.
exact le_wd.
Qed.

(* This produces a warning about a morphism redeclaration. Why is not
there a warning after declaring lt? *)

Theorem le_lt : forall x y, le x y <-> lt x y \/ x == y.
Proof.
exact le_lt.
Qed.

Theorem lt_0 : forall x, ~ (lt x 0).
Proof.
exact lt_0.
Qed.

Theorem lt_S : forall x y, lt x (S y) <-> le x y.
Proof.
exact lt_S.
Qed.

End NDefaultOrderModule.

Module Export DefaultTimesOrderProperties :=
  NTimesOrderProperties NDefaultTimesModule NDefaultOrderModule.

End MiscFunctFunctor.
