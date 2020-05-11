Notation aid := (@id) (only parsing).
Notation idn := id (only parsing).
Ltac unfold_id := unfold id.

Fixpoint fact (n : nat)
  := match n with
     | 0 => 1
     | S n => (S n) * fact n
     end.

Opaque id.
Goal id (fact 100) = fact 100.
  Strategy expand [id].
  Time Timeout 5 reflexivity. (* should be instant *)
  (* Finished transaction in 0. secs (0.u,0.s) (successful) *)
Time Timeout 5 Defined.
(* Finished transaction in 0.001 secs (0.u,0.s) (successful) *)

Goal True.
  let x := smart_global:(id) in unfold x.
  let x := smart_global:(aid) in unfold x.
  let x := smart_global:(idn) in unfold x.
Abort.

Goal id 0 = 0.
  Opaque id.
  assert_fails unfold_id.
  Transparent id.
  assert_succeeds unfold_id.
  Opaque id.
  Strategy 0 [id].
  assert_succeeds unfold_id.
  Strategy 1 [id].
  assert_succeeds unfold_id.
  Strategy -1 [id].
  assert_succeeds unfold_id.
  Strategy opaque [id].
  assert_fails unfold_id.
  Strategy transparent [id].
  assert_succeeds unfold_id.
  Opaque id.
  Strategy expand [id].
  assert_succeeds unfold_id.
  reflexivity.
Qed.
Goal id 0 = 0.
  Opaque aid.
  assert_fails unfold_id.
  Transparent aid.
  assert_succeeds unfold_id.
  Opaque aid.
  Strategy 0 [aid].
  assert_succeeds unfold_id.
  Strategy 1 [aid].
  assert_succeeds unfold_id.
  Strategy -1 [aid].
  assert_succeeds unfold_id.
  Strategy opaque [aid].
  assert_fails unfold_id.
  Strategy transparent [aid].
  assert_succeeds unfold_id.
  Opaque aid.
  Strategy expand [aid].
  assert_succeeds unfold_id.
  reflexivity.
Qed.
Goal id 0 = 0.
  Opaque idn.
  assert_fails unfold_id.
  Transparent idn.
  assert_succeeds unfold_id.
  Opaque idn.
  Strategy 0 [idn].
  assert_succeeds unfold_id.
  Strategy 1 [idn].
  assert_succeeds unfold_id.
  Strategy -1 [idn].
  assert_succeeds unfold_id.
  Strategy opaque [idn].
  assert_fails unfold_id.
  Strategy transparent [idn].
  assert_succeeds unfold_id.
  Opaque idn.
  Strategy expand [idn].
  assert_succeeds unfold_id.
  reflexivity.
Qed.
