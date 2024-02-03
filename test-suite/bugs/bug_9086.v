(* Systematic study around issue #9086 *)

Local Set Primitive Projections.
Record pair {A B} := mk { _1 : A; _2 : B _1 }.

Module Folded.

Goal (@mk Prop (fun _ => Prop) True True).(_1).
  assert_succeeds (progress (cbn iota delta [_1])).
  assert_succeeds (progress (cbv iota delta [_1])).
  assert_succeeds (progress (lazy iota delta [_1])).
  assert_succeeds (progress simpl).
Opaque _1. (* has an impact on "_1" *)
  assert_fails (progress cbn).
  assert_fails (progress cbv).
  assert_fails (progress lazy).
  assert_fails (progress simpl).
Abort.

End Folded.

Module Unfolded.

Goal (@mk Prop (fun _ => Prop) True True).(_1).
  lazy delta [_1]. (* move to unfolded form *)
  assert_succeeds (progress (cbn iota delta [_1])).
  assert_succeeds (progress (cbv iota delta [_1])).
  assert_succeeds (progress (lazy iota delta [_1])).
  assert_succeeds (progress simpl).
Opaque _1. (* no impact on "unfolded _1" *)
  assert_succeeds (progress (cbn iota delta [_1])).
  assert_succeeds (progress (cbv iota delta [_1])).
  assert_succeeds (progress (lazy iota delta [_1])).
  assert_succeeds (progress simpl).
Abort.

End Unfolded.

Module Unfold.

Set Printing Unfolded Projection As Match.
Goal (@mk Prop (fun _ => Prop) True True).(_1).
  cbv delta [_1]. (* should internally unfold the projection *)
  progress lazy iota. (* allowed by the unfolding *)
Abort.

End Unfold.
