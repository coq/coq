From Corelib.Program Require Import Wf.

(* A transparent well-founded relation and a dependent result. *)
Definition predecessor (m n : nat) := n = S m.
Definition result n := {k : nat | k = n}.

Lemma predecessor_wf : well_founded predecessor.
Proof.
  intro n; induction n as [|n IH]; constructor; intros m H.
  - discriminate H.
  - unfold predecessor in H; injection H as H; subst m; exact IH.
Defined.

Definition step n (rec : forall m, predecessor m n -> result m) : result n.
Proof.
  destruct n as [|m].
  - exact (exist _ 0 eq_refl).
  - destruct (rec m eq_refl) as [k H].
    exact (exist _ (S k) (f_equal S H)).
Defined.

(* Fix computes with a transparent accessibility proof. *)
Definition count := @Init.Wf.Fix nat predecessor predecessor_wf result step.
Example fix_compute : proj1_sig (count 3) = 3.
Proof. reflexivity. Qed.

(* Fix_F_2 computes over pairs with a dependent result. *)
Definition pair_relation (p q : nat * nat) := predecessor (fst p) (fst q).
Definition pair_wf := @measure_wf (nat * nat) nat predecessor predecessor_wf (@fst nat nat).
Definition pair_step n j (rec : forall m k, pair_relation (m,k) (n,j) -> result m) := step n (fun m h => rec m j h).
Definition pair_count n j := @Fix_F_2 nat nat pair_relation (fun n _ => result n) pair_step n j (pair_wf (n,j)).
Example fix_pair_compute : proj1_sig (pair_count 3 2) = 3.
Proof. reflexivity. Qed.

(* Fix_sub computes with arguments packaged as subsets. *)
Definition sub_step n (rec : forall m : {m | predecessor m n}, result (proj1_sig m)) := step n (fun m h => rec (exist _ m h)).
Definition sub_count := @Fix_sub nat predecessor predecessor_wf result sub_step.
Example fix_sub_compute : proj1_sig (sub_count 3) = 3.
Proof. reflexivity. Qed.

(* Equation lemmas work with opaque accessibility proofs. *)
Lemma predecessor_wf_opaque : well_founded predecessor.
Proof. exact predecessor_wf. Qed.

Lemma step_ext n (f g : forall m, predecessor m n -> result m) : (forall m h, f m h = g m h) -> step n f = step n g.
Proof. intro H; destruct n; simpl; [reflexivity | rewrite H; reflexivity]. Qed.
Lemma sub_step_ext n (f g : forall m : {m | predecessor m n}, result (proj1_sig m)) : (forall m, f m = g m) -> sub_step n f = sub_step n g.
Proof. intro H; apply step_ext; intros m h; exact (H (exist _ m h)). Qed.

Definition opaque_count := @Init.Wf.Fix nat predecessor predecessor_wf_opaque result step.
Example fix_equation n : opaque_count n = step n (fun m _ => opaque_count m).
Proof. exact (@Init.Wf.Fix_eq nat predecessor predecessor_wf_opaque result step step_ext n). Qed.

Definition opaque_sub_count := @Fix_sub nat predecessor predecessor_wf_opaque result sub_step.
Example fix_sub_equation n : opaque_sub_count n = sub_step n (fun m => opaque_sub_count (proj1_sig m)).
Proof. exact (@Program.Wf.Fix_eq nat predecessor predecessor_wf_opaque result sub_step sub_step_ext n). Qed.

(* Keep Program obligations transparent for computation. *)
Set Transparent Obligations.
Local Obligation Tactic := intros; subst; try reflexivity; try apply predecessor_wf; try (apply measure_wf; apply predecessor_wf).

(* Program recursion with an explicit well-founded relation. *)
Program Fixpoint program_wf (n : nat) {wf predecessor n} : nat :=
  match n with 0 => 0 | S m => S (program_wf m) end.
Example program_wf_compute : program_wf 3 = 3.
Proof. reflexivity. Qed.

(* Program recursion with a measure. *)
Program Fixpoint program_measure (n : nat) {measure n predecessor} : nat :=
  match n with 0 => 0 | S m => S (program_measure m) end.
Example program_measure_compute : program_measure 3 = 3.
Proof. reflexivity. Qed.
