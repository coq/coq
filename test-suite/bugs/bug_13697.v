From Coq Require micromega.Lia Lists.List Program.Program.

Set Implicit Arguments.
Set Strict Implicit. Set Strongly Strict Implicit.
Set Maximal Implicit Insertion.

Section Context.

Import Lia List Tactics.
Import ListNotations.

Obligation Tactic := idtac.

Program Fixpoint merge (A : Type) (f : A -> A -> bool) (l0 l1 : list A)
  {measure (length l0 + length l1)} : list A :=
  match l0, l1 with
  | [], _ => l1
  | _, [] => l0
  | n0 :: k0, n1 :: k1 => if f n0 n1 then
    n0 :: merge f k0 l1 else
    n1 :: @merge _ f l0 k1
  end.
Next Obligation. intros; subst; cbn in *; lia. Qed.
Next Obligation. intros; subst; cbn in *; lia. Qed.
Next Obligation. program_simplify. Qed.
Next Obligation. program_solve_wf. Defined.

End Context.

Section Context.

Import List NArith.
Import ListNotations N.

Open Scope N_scope.

Compute merge leb [7; 13; 42] [18; 69; 420].

End Context.
