Set Primitive Projections.

Record Box (A:Type) := box { unbox : A }.

Definition ubox := @unbox.

Axiom trip : nat -> nat -> nat -> Prop.

Ltac show_goal := match goal with |- ?g => idtac g end.

Lemma foo (n:Box nat) :
  (* constant, folded, unfolded *)
    trip (ubox _ n) (unbox _ n) (match n with box _ n => n end).
Proof.
  simpl. (* remove extra letins introduced by match compilation *)
  cbv delta [ubox].
  show_goal.

  Set Printing Unfolded Projection As Match.
  show_goal.

  Set Printing Projections.
  show_goal.

  Unset Printing Unfolded Projection As Match.
  show_goal.

  Arguments unbox {_}.
  show_goal.

  Set Printing Unfolded Projection As Match.
  show_goal.

  Unset Printing Projections.
  show_goal.
Abort.
