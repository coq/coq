(* Before 31a69c4d0fd7b8325187e8da697a9c283594047d, [case] would stack overflow *)
Require Import Arith.

Section Acc_generator.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  (* *Lazily* add 2^n - 1 Acc_intro on top of wf.
     Needed for fast reductions using Function and Program Fixpoint
     and probably using Fix and Fix_F_2
   *)
  Fixpoint Acc_intro_generator n (wf : well_founded R)  :=
    match n with
        | O => wf
        | S n => fun x => Acc_intro x (fun y _ => Acc_intro_generator n (Acc_intro_generator n wf) y)
    end.


End Acc_generator.

Definition pred_F : (forall x : nat,
        (forall y : nat, y < x -> (fun _ : nat => nat) y) ->
        (fun _ : nat => nat) x).
Proof.
  intros x.
  simpl.
  case x.
  exact (fun _ => 0).
  intros n h.
  apply (h n).
  constructor.
Defined.

Definition my_pred :=  Fix lt_wf (fun _ => nat) pred_F.


Lemma my_pred_is_pred : forall x, match my_pred x with | 0 => True | S n => False end.
Proof.
  intros x.
  case x.
Abort.

Definition my_pred_bad :=  Fix (Acc_intro_generator _ _ 100 lt_wf) (fun _ => nat) pred_F.

Lemma my_pred_is_pred : forall x, match my_pred_bad x with | 0 => True | S n => False end.
Proof.
  intros x.
  Timeout 2 case x.
Admitted.
