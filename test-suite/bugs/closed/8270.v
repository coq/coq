(* Don't do zeta in cbn when not asked for *)

Goal let x := 0 in
     let y := x in
     y = 0.
  (* We use "cofix" as an example because there are obviously no
     cofixpoints in sight.  This problem arises with any set of
     reduction flags (not including zeta where the lets are of course reduced away) *)
  cbn cofix.
  intro x.
  unfold x at 1. (* Should succeed *)
  Undo 2.
  cbn zeta.
  Fail unfold x at 1.
Abort.
