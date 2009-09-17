(* -*- coq-prog-args: ("-emacs-U" "-debug") -*- *)
Require Import Coq.Program.Program.
Require Import List.

Set Implicit Arguments.

Section Accessors.
  Variable A : Set.

  Program Definition myhd : forall (l : list A | length l <> 0), A :=
    fun l =>
      match l with
        | nil => !
        | hd :: tl => hd
      end.

  Program Definition mytail (l : list A | length l <> 0) : list A :=
    match l with
      | nil => !
      | hd :: tl => tl
    end.
End Accessors.

Program Definition test_hd : nat := myhd (cons 1 nil).

(*Eval compute in test_hd*)
(*Program Definition test_tail : list A := mytail nil.*)

Section app.
  Variable A : Set.

  Program Fixpoint app (l : list A) (l' : list A) { struct l } :
    { r : list A | length r = length l + length l' } :=
    match l with
      | nil => l'
      | hd :: tl => hd :: (tl ++ l')
    end
    where "x ++ y" := (app x y).

  Next Obligation.
    intros.
    destruct_call app ; program_simpl.
  Defined.

  Program Lemma app_id_l : forall l : list A, l = nil ++ l.
  Proof.
    simpl ; auto.
  Qed.

  Program Lemma app_id_r : forall l : list A, l = l ++ nil.
  Proof.
    induction l ; simpl in * ; auto.
    rewrite <- IHl ; auto.
  Qed.

End app.

Extraction app.

Section Nth.

  Variable A : Set.

  Program Fixpoint nth (l : list A) (n : nat | n < length l) { struct l } : A :=
    match n, l with
      | 0, hd :: _ => hd
      | S n', _ :: tl => nth tl n'
      | _, nil => !
    end.

  Next Obligation.
  Proof.
    simpl in *. auto with arith.
  Defined.

  Next Obligation.
  Proof.
    inversion H.
  Qed.

  Program Fixpoint nth' (l : list A) (n : nat | n < length l) { struct l } : A :=
    match l, n with
      | hd :: _, 0 => hd
      | _ :: tl, S n' => nth' tl n'
      | nil, _ => !
    end.
  Next Obligation.
  Proof.
    simpl in *. auto with arith.
  Defined.

  Next Obligation.
  Proof.
    intros.
    inversion H.
  Defined.

End Nth.

