Fixpoint fib n := match n with
  | O => 1
  | S m => match m with
    | O => 1
    | S o => fib o + fib m end end.

Ltac sleep n :=
  try (cut (fib n = S (fib n)); reflexivity).

Let time := 15.

(* BEGIN MINI DEMO *)
(* JUMP TO "JUMP HERE" *)

Lemma a : True.
Proof.
  sleep time.
  idtac.
  sleep time.
  exact (I I).
Qed.

Lemma b : True.
Proof. 
  sleep time.
  idtac.
  (* change in semantics: Print a. *)
  sleep time.
  exact a.
Qed. (* JUMP HERE *)

Lemma work_here : True.
Proof.
cut True.
Abort.

(* END MINI DEMO *)

Require Import Unicode.Utf8.
Notation "a ⊃ b" := (a → b) (at level 91, left associativity).

Definition untrue := False.

Section Ex.
Variable P Q : Prop.
Implicit Types X Y : Prop.
Hypothesis CL : forall X Y, (X → ¬Y → untrue) → (¬X ∨ Y).

Lemma  Peirce : P ⊃ Q ⊃ P ⊃ P.
Proof (* using P Q CL. *).   (* Uncomment -> more readable *)
intro pqp.

  Remark EM : ¬P ∨ P.
  Proof using P CL.
  intros; apply CL; intros p np.
  Fail progress auto.  (* Missing hint *)

  (* Try commenting this out *)
  Hint Extern 0 => match goal with
    p : P, np : ¬P |- _ => case (np p)
  end.

  auto.  (* This line requires the hint above *)
  Qed.

case EM; auto.  (* This line requires the hint above *)
Qed.

End Ex.

Check EM. (* Print EM. *)


Axiom exM : forall P, P \/ ~P.

Lemma CPeirce (P Q : Prop) : P ⊃ Q ⊃ P ⊃ P.
Proof.
apply Peirce.
intros.
case (exM X); auto.
intro; right.
case (exM Y); auto; intro.
case H; auto.
Qed.

Require Import Recdef.

Definition m (n : nat) := n.

Function f (n : nat) {measure m n} : bool :=
  match n with
  | O => true
  | S x => f (x + 0)
  end.
Proof.
intros x y _. unfold m.
rewrite <- plus_n_O. auto.
Qed.
