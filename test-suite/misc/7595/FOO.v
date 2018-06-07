Require Import Test.base.

Lemma dec_stable `{Decision P} : ¬¬P → P.
Proof. firstorder. Qed.

(** The tactic [destruct_decide] destructs a sumbool [dec]. If one of the
components is double negated, it will try to remove the double negation. *)
Tactic Notation "destruct_decide" constr(dec) "as" ident(H) :=
  destruct dec as [H|H];
  try match type of H with
  | ¬¬_ => apply dec_stable in H
  end.
Tactic Notation "destruct_decide" constr(dec) :=
  let H := fresh in destruct_decide dec as H.


(** * Monadic operations *)
Instance option_guard: MGuard option := λ P dec A f,
  match dec with left H => f H | _ => None end.

(** * Tactics *)
Tactic Notation "case_option_guard" "as" ident(Hx) :=
  match goal with
  | H : context C [@mguard option _ ?P ?dec] |- _ =>
    change (@mguard option _ P dec) with (λ A (f : P → option A),
      match @decide P dec with left H' => f H' | _ => None end) in *;
    destruct_decide (@decide P dec) as Hx
  | |- context C [@mguard option _ ?P ?dec] =>
    change (@mguard option _ P dec) with (λ A (f : P → option A),
      match @decide P dec with left H' => f H' | _ => None end) in *;
    destruct_decide (@decide P dec) as Hx
  end.
Tactic Notation "case_option_guard" :=
  let H := fresh in case_option_guard as H.

(* This proof failed depending on the name of the module. *)
Lemma option_guard_True {A} P `{Decision P} (mx : option A) :
  P → (guard P; mx) = mx.
Proof. intros. case_option_guard. reflexivity. contradiction. Qed.
