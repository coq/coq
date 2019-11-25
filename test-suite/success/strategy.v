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
Opaque id.
Goal id 0 = 0.
  strategy opaque [id].
  strategy opaque [id id].
  assert_fails unfold_id.
  strategy transparent [id].
  assert_succeeds unfold_id.
  strategy opaque [id].
  strategy 0 [id].
  assert_succeeds unfold_id.
  strategy 1 [id].
  assert_succeeds unfold_id.
  strategy -1 [id].
  assert_succeeds unfold_id.
  strategy opaque [id].
  assert_fails unfold_id.
  strategy transparent [id].
  assert_succeeds unfold_id.
  strategy opaque [id].
  strategy expand [id].
  assert_succeeds unfold_id.
  let l := strategy_level:(expand) in
  strategy l [id].
  let idx := smart_global:(id) in
  cbv [idx].
  (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       strategy expand [idx].
  reflexivity.
Qed.
Goal id 0 = 0.
  strategy opaque [aid].
  assert_fails unfold_id.
  strategy transparent [aid].
  assert_succeeds unfold_id.
  strategy opaque [aid].
  strategy 0 [aid].
  assert_succeeds unfold_id.
  strategy 1 [aid].
  assert_succeeds unfold_id.
  strategy -1 [aid].
  assert_succeeds unfold_id.
  strategy opaque [aid].
  assert_fails unfold_id.
  strategy transparent [aid].
  assert_succeeds unfold_id.
  strategy opaque [aid].
  strategy expand [aid].
  assert_succeeds unfold_id.
  reflexivity.
Qed.
Goal id 0 = 0.
  strategy opaque [idn].
  assert_fails unfold_id.
  strategy transparent [idn].
  assert_succeeds unfold_id.
  strategy opaque [idn].
  strategy 0 [idn].
  assert_succeeds unfold_id.
  strategy 1 [idn].
  assert_succeeds unfold_id.
  strategy -1 [idn].
  assert_succeeds unfold_id.
  strategy opaque [idn].
  assert_fails unfold_id.
  strategy transparent [idn].
  assert_succeeds unfold_id.
  strategy opaque [idn].
  strategy expand [idn].
  assert_succeeds unfold_id.
  reflexivity.
Qed.

(* test that strategy tactic does not persist after the proof *)
Opaque id.
Goal id 0 = 0.
  strategy transparent [id].
  assert_succeeds unfold_id.
  reflexivity.
Qed.
Goal id 0 = 0.
  assert_fails unfold_id.
  reflexivity.
Qed.

(* test that the strategy tactic does persist through abstract *)
Opaque id.
Goal id 0 = 0.
  strategy expand [id].
  Time Timeout 5 assert (id (fact 100) = fact 100) by abstract reflexivity.
  reflexivity.
Time Timeout 5 Defined.

(* test that [strategy] plays well with [;] *)
Goal id 0 = 0.
  Fail let id' := id in unfold id'.
  try (tryif (let id' := id in
              strategy expand [id]; unfold id') then fail else fail 1).
  Fail let id' := id in unfold id'.
  assert_succeeds (let id' := id in strategy expand [id]; unfold id').
  (* [unfold id] should fail, but does not, because [strategy] plays poorly with [assert_succeeds] *)
  Fail Fail unfold id.
  reflexivity.
Defined.
Opaque id.
Goal id 0 = 0.
  Time Timeout 5 (strategy expand [id];
                 assert (id (fact 100) = fact 100) by abstract reflexivity).
  reflexivity.
Time Timeout 5 Defined.

(* check that module substitutions happen correctly *)
Module F.
  Definition id {T} := @id T.
  Opaque id.
  Ltac transparent_id := strategy transparent [id].
End F.
Opaque F.id.

Goal F.id 0 = F.id 0.
  Fail unfold F.id.
  F.transparent_id.
  progress unfold F.id.
Abort.

Module Type Empty. End Empty.
Module E. End E.
Module F2F (E : Empty).
  Definition id {T} := @id T.
  Opaque id.
  Ltac transparent_id := strategy transparent [id].
End F2F.
Module F2 := F2F E.
Opaque F2.id.

Goal F2.id 0 = F2.id 0.
  Fail unfold F2.id.
  F2.transparent_id.
  progress unfold F2.id.
Abort.

(* test the tactic notation entries *)
Tactic Notation "set_strategy0" strategy_level(l) "[" ne_smart_global_list(v) "]" := strategy l [ v ].
Tactic Notation "set_strategy1" strategy_level_or_var(l) "[" ne_smart_global_list(v) "]" := strategy l [ v ].
Tactic Notation "set_strategy2" strategy_level(l) "[" constr(v) "]" := strategy l [ v ].
Tactic Notation "set_strategy3" strategy_level_or_var(l) "[" constr(v) "]" := strategy l [ v ].

(* [set_strategy0] should work, but it doesn't, due to a combination of https://github.com/coq/coq/issues/11202 and https://github.com/coq/coq/issues/11209 *)
Opaque id.
Goal id 0 = 0.
  Fail (* should work, not Fail *) set_strategy0 opaque [id].
  Fail (* should work, not Fail *) set_strategy0 opaque [id id].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy0 transparent [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [id].
  Fail (* should work, not Fail *) set_strategy0 0 [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 1 [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 -1 [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [id].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy0 transparent [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [id].
  Fail (* should work, not Fail *) set_strategy0 expand [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       set_strategy0 expand [idx].
  reflexivity.
Qed.
Goal id 0 = 0.
  Fail (* should work, not Fail *) set_strategy0 opaque [aid].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy0 transparent [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [aid].
  Fail (* should work, not Fail *) set_strategy0 0 [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 1 [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 -1 [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [aid].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy0 transparent [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [aid].
  Fail (* should work, not Fail *) set_strategy0 expand [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  reflexivity.
Qed.
Goal id 0 = 0.
  Fail (* should work, not Fail *) set_strategy0 opaque [idn].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy0 transparent [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [idn].
  Fail (* should work, not Fail *) set_strategy0 0 [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 1 [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 -1 [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [idn].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy0 transparent [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy0 opaque [idn].
  Fail (* should work, not Fail *) set_strategy0 expand [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  reflexivity.
Qed.

(* [set_strategy1] should work, but it doesn't, due to a combination of https://github.com/coq/coq/issues/11202 and https://github.com/coq/coq/issues/11209 *)
Opaque id.
Goal id 0 = 0.
  Fail (* should work, not Fail *) set_strategy1 opaque [id].
  Fail (* should work, not Fail *) set_strategy1 opaque [id id].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy1 transparent [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [id].
  Fail (* should work, not Fail *) set_strategy1 0 [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 1 [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 -1 [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [id].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy1 transparent [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [id].
  Fail (* should work, not Fail *) set_strategy1 expand [id].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) let l := strategy_level:(expand) in
                                   set_strategy1 l [id].
  (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       set_strategy1 expand [idx].
  reflexivity.
Qed.
Goal id 0 = 0.
  Fail (* should work, not Fail *) set_strategy1 opaque [aid].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy1 transparent [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [aid].
  Fail (* should work, not Fail *) set_strategy1 0 [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 1 [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 -1 [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [aid].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy1 transparent [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [aid].
  Fail (* should work, not Fail *) set_strategy1 expand [aid].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  reflexivity.
Qed.
Goal id 0 = 0.
  Fail (* should work, not Fail *) set_strategy1 opaque [idn].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy1 transparent [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [idn].
  Fail (* should work, not Fail *) set_strategy1 0 [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 1 [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 -1 [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [idn].
  assert_fails unfold_id.
  Fail (* should work, not Fail *) set_strategy1 transparent [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  Fail (* should work, not Fail *) set_strategy1 opaque [idn].
  Fail (* should work, not Fail *) set_strategy1 expand [idn].
  Fail (* should work, not Fail *) assert_succeeds unfold_id.
  reflexivity.
Qed.

Opaque id.
Goal id 0 = 0.
  set_strategy2 opaque [id].
  assert_fails unfold_id.
  set_strategy2 transparent [id].
  assert_succeeds unfold_id.
  set_strategy2 opaque [id].
  set_strategy2 0 [id].
  assert_succeeds unfold_id.
  set_strategy2 1 [id].
  assert_succeeds unfold_id.
  set_strategy2 -1 [id].
  assert_succeeds unfold_id.
  set_strategy2 opaque [id].
  assert_fails unfold_id.
  set_strategy2 transparent [id].
  assert_succeeds unfold_id.
  set_strategy2 opaque [id].
  set_strategy2 expand [id].
  assert_succeeds unfold_id.
  (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       set_strategy2 expand [idx].
  reflexivity.
Qed.
Goal id 0 = 0.
  set_strategy2 opaque [aid].
  assert_fails unfold_id.
  set_strategy2 transparent [aid].
  assert_succeeds unfold_id.
  set_strategy2 opaque [aid].
  set_strategy2 0 [aid].
  assert_succeeds unfold_id.
  set_strategy2 1 [aid].
  assert_succeeds unfold_id.
  set_strategy2 -1 [aid].
  assert_succeeds unfold_id.
  set_strategy2 opaque [aid].
  assert_fails unfold_id.
  set_strategy2 transparent [aid].
  assert_succeeds unfold_id.
  set_strategy2 opaque [aid].
  set_strategy2 expand [aid].
  assert_succeeds unfold_id.
  reflexivity.
Qed.
Goal id 0 = 0.
  set_strategy2 opaque [idn].
  assert_fails unfold_id.
  set_strategy2 transparent [idn].
  assert_succeeds unfold_id.
  set_strategy2 opaque [idn].
  set_strategy2 0 [idn].
  assert_succeeds unfold_id.
  set_strategy2 1 [idn].
  assert_succeeds unfold_id.
  set_strategy2 -1 [idn].
  assert_succeeds unfold_id.
  set_strategy2 opaque [idn].
  assert_fails unfold_id.
  set_strategy2 transparent [idn].
  assert_succeeds unfold_id.
  set_strategy2 opaque [idn].
  set_strategy2 expand [idn].
  assert_succeeds unfold_id.
  reflexivity.
Qed.

Opaque id.
Goal id 0 = 0.
  set_strategy3 opaque [id].
  assert_fails unfold_id.
  set_strategy3 transparent [id].
  assert_succeeds unfold_id.
  set_strategy3 opaque [id].
  set_strategy3 0 [id].
  assert_succeeds unfold_id.
  set_strategy3 1 [id].
  assert_succeeds unfold_id.
  set_strategy3 -1 [id].
  assert_succeeds unfold_id.
  set_strategy3 opaque [id].
  assert_fails unfold_id.
  set_strategy3 transparent [id].
  assert_succeeds unfold_id.
  set_strategy3 opaque [id].
  set_strategy3 expand [id].
  assert_succeeds unfold_id.
  let l := strategy_level:(expand) in
  set_strategy3 l [id].
  (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       set_strategy3 expand [idx].
  reflexivity.
Qed.
Goal id 0 = 0.
  set_strategy3 opaque [aid].
  assert_fails unfold_id.
  set_strategy3 transparent [aid].
  assert_succeeds unfold_id.
  set_strategy3 opaque [aid].
  set_strategy3 0 [aid].
  assert_succeeds unfold_id.
  set_strategy3 1 [aid].
  assert_succeeds unfold_id.
  set_strategy3 -1 [aid].
  assert_succeeds unfold_id.
  set_strategy3 opaque [aid].
  assert_fails unfold_id.
  set_strategy3 transparent [aid].
  assert_succeeds unfold_id.
  set_strategy3 opaque [aid].
  set_strategy3 expand [aid].
  assert_succeeds unfold_id.
  reflexivity.
Qed.
Goal id 0 = 0.
  set_strategy3 opaque [idn].
  assert_fails unfold_id.
  set_strategy3 transparent [idn].
  assert_succeeds unfold_id.
  set_strategy3 opaque [idn].
  set_strategy3 0 [idn].
  assert_succeeds unfold_id.
  set_strategy3 1 [idn].
  assert_succeeds unfold_id.
  set_strategy3 -1 [idn].
  assert_succeeds unfold_id.
  set_strategy3 opaque [idn].
  assert_fails unfold_id.
  set_strategy3 transparent [idn].
  assert_succeeds unfold_id.
  set_strategy3 opaque [idn].
  set_strategy3 expand [idn].
  assert_succeeds unfold_id.
  reflexivity.
Qed.
