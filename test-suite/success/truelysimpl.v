Require Import Setoid.
Require Import Force.Force.
Require Import Ltac2.Ltac2.

Set Default Proof Mode "Classic".

Module Logic.
  Lemma iff_trivial (P : Prop) : P <-> P.
  Proof. split; intros H; exact H. Qed.

  Lemma and_comm (P1 P2 : Prop) : P1 /\ P2 <-> P2 /\ P1.
  Proof.
    split.
    - intros [H1 H2]; split; [exact H2 | exact H1].
    - intros [H2 H1]; split; [exact H1 | exact H2].
  Qed.

  Lemma and_true (P : Prop) : P /\ True <-> P.
  Proof.
    split.
    - intros [HP _]. exact HP.
    - intros HP. split; [exact HP| exact I].
  Qed.

  Lemma true_and (P : Prop) : True /\ P <-> P.
  Proof. rewrite and_comm. rewrite and_true. apply iff_trivial. Qed.

  Lemma and_false (P : Prop) : P /\ False <-> False.
  Proof.
    split.
    - intros [_ HF]. exact HF.
    - intros HF. exfalso. exact HF.
  Qed.

  Lemma false_and (P : Prop) : False /\ P <-> False.
  Proof. rewrite and_comm. rewrite and_false. apply iff_trivial. Qed.
End Logic.

Inductive prop :=
  | conj  : prop -> prop -> prop
  | true  : prop
  | false : prop
  | inj   : Blocked Prop -> prop.

Fixpoint reflect (p : prop) : Blocked Prop :=
  match p with
  | conj p1 p2 => block ((unblock (reflect p1)) /\ (unblock (reflect p2)))
  | true       => block True
  | false      => block False
  | inj P      => P
  end.

Eval lazy in reflect (conj true (inj (block (1 + 1 = 2)))).

Ltac2 rec reify (p : constr) : constr :=
  lazy_match! p with
  | ?p1 /\ ?p2 => let p1 := reify p1 in let p2 := reify p2 in '(conj $p1 $p2)
  | True       => '(true)
  | False      => '(false)
  | ?p         => '(inj (block $p))
  end.

Fixpoint simplify (p : prop) : prop :=
  match p with
  | conj p1 p2 =>
      match simplify p1 with
      | true  => simplify p2
      | false => false
      | p1    =>
          match simplify p2 with
          | true  => p1
          | false => false
          | p2    => conj p1 p2
          end
      end
  | _ => p
  end.

Lemma simplify_ok (p : prop) : unblock (reflect (simplify p)) <-> unblock (reflect p).
Proof.
  induction p; lazy -[iff]; fold simplify reflect.
  - rewrite <-IHp1; clear IHp1.
    rewrite <-IHp2; clear IHp2.
    destruct (simplify p1); lazy -[iff]; fold simplify reflect.
    + destruct (simplify p2); lazy -[iff]; fold simplify reflect.
      * apply Logic.iff_trivial.
      * rewrite Logic.and_true. apply Logic.iff_trivial.
      * rewrite Logic.and_false. apply Logic.iff_trivial.
      * apply Logic.iff_trivial.
    + rewrite Logic.true_and. apply Logic.iff_trivial.
    + rewrite Logic.false_and. apply Logic.iff_trivial.
    + destruct (simplify p2); lazy -[iff]; fold simplify reflect.
      * apply Logic.iff_trivial.
      * rewrite Logic.and_true. apply Logic.iff_trivial.
      * rewrite Logic.and_false. apply Logic.iff_trivial.
      * apply Logic.iff_trivial.
  - apply Logic.iff_trivial.
  - apply Logic.iff_trivial.
  - apply Logic.iff_trivial.
Qed.

Lemma simplify_ok_run (p : prop) :
  run (block (unblock (reflect (simplify p)) -> unblock (reflect p))) (fun x => x).
Proof. lazy; fold reflect simplify. apply simplify_ok. Qed.

Ltac2 truely_simplify (p : constr) : unit :=
  let reified := reify p in
  let p := '(simplify_ok_run $reified _) in
  refine p.

Ltac truely_simplify :=
  let truely_simplify :=
    ltac2:(p |- truely_simplify (Option.get (Ltac1.to_constr p)))
  in
  lazymatch goal with |- ?p => unshelve truely_simplify p end.

Goal True /\ (True /\ 1 + 1 = 2) /\ (True /\ True /\ 2 + 1 = 3).
Proof.
  truely_simplify.
  lazymatch goal with |- 1 + 1 = 2 /\ 2 + 1 = 3 => idtac | _ => fail "Error" end.
  split; reflexivity.
Qed.
