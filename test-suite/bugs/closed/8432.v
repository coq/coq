Require Import Program.Tactics.

Obligation Tactic := idtac.
Set Universe Polymorphism.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Inductive Empty : Type :=.
Inductive Unit : Type := tt.
Definition not (A : Type) := A -> Empty.

  Lemma nat_path_O_S (n : nat) (H : paths O (S n)) : Empty.
  Proof. refine (
    match H in paths _ i return
      match i with
      | O => Unit
      | S _ => Empty
      end
    with
    | idpath _ => tt
    end
  ). Defined.
  Lemma symmetry {A} (x y : A) (p : paths x y) : paths y x.
  Proof.
    destruct p. apply idpath.
  Defined.
  Lemma nat_path_S_O (n : nat) (H : paths (S n) O) : Empty.
  Proof. eapply nat_path_O_S. exact (symmetry _ _ H). Defined.
Set Printing Universes.
Program Fixpoint succ_not_zero (n:nat) : not (paths (S n) 0) :=
match n as n return not (paths (S n) 0) with
| 0 => nat_path_S_O _
| S n' => let dummy := succ_not_zero n' in _
end.
Next Obligation.
  intros f _ n dummy H. exact (nat_path_S_O _ H).
  Show Universes.
Defined.
