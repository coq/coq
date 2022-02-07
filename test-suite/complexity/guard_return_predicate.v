(* Testk that we don't unfold unnecessarily in guard condition the
   body of a return predicate *)
(* Expected time < 1.00s *)

Fixpoint slow n : Type -> Type :=
  match n with
  | 0 => fun A => A
  | S k => fun A => slow k (slow k A)
  end.

Parameter y : unit.
Parameter h : slow 100 nat -> nat.

Timeout 5 Time Fixpoint F (g:nat->slow 100 nat) n : nat :=
  match n with
  | 0 => 0
  | S k => (fun x => h (match y return slow 100 nat with tt => g (F g x) end)) k
  end.
