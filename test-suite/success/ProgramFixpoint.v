Require Import Program.Basics Program.Tactics.

Module ProgramFixProto.

(* Check the presence of [fix_proto] so that a preliminary work done on
   obligations can be done automatically *)

Program Fixpoint do_bug m : { k : nat | exists u : nat, k = m }  :=
  match m with
  | 0 => 0
  | S m' => S (do_bug m')
  end.
Next Obligation.
  exists 0.
  reflexivity.
Qed.
Next Obligation.
  exists 0.
  reflexivity.
Defined.

End ProgramFixProto.
