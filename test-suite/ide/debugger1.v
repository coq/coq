(* Ltac1 manual tests *)
Set Ltac Debug.
Set Ltac Debug History 100.

Module Abbrev.
Ltac a_x := split; apply I; idtac.
Ltac b_x := a_x.
Goal True /\ True.
b_x.
Abort.
End Abbrev.

(* proof diffs
   Outside Ltac*, proof diffs compare the state before the last effectful
   tactic with the state before the current tactic.  In Ltac*, proof diffs
   compare relative to the last effectful tactic in the same function.

   expected results:
   1,6 - beginning of an Ltac* tactic, nothing highlighted
   2,4 - one goal not highlighted (OK for now)
   3   - first two goals highlighted, third goal is not
   5   - last two goals highlighted, first two are not
   7,8 - four goals highlighted, "n : nat" not highlighted
single step
bug (?)

*)
Module Diffs.
Goal forall n: nat, (1 = 1 /\ 2 = 2) /\
    (False /\ True).
Ltac my_split := (* 1 *) split; only 1: (* 2 *) split;
    (* 3 *) only 3: (* 4 *) split; (* 5 *) idtac.
Ltac xx := (* 6 *) my_split; (* 7 *) idtac.
intro; xx; (* 8 *)idtac.
Abort.
End Diffs.

Module LetWithTactic.
(* Several problems when the rhs of a let
   is a tactic:
   - extra stop at call of z
   - stops in defn of m for the let
   - doesn't stop in m when executing w
     (adding a parm to m and using the call "m ()"
      does stop in m)
*)

Ltac m := idtac "m".

Goal True.
Ltac z := let w := m in
  w.

z.
Abort.
End LetWithTactic.
