Notation aid := (@id) (only parsing).
Notation idn := id (only parsing).
Ltac unfold_id := unfold id.

Fixpoint fact (n : nat)
  := match n with
     | 0 => 1
     | S n => (S n) * fact n
     end.

Opaque id.
Goal id 0 = 0.
  with_strategy
    opaque [id]
    (with_strategy
       opaque [id id]
       (assert_fails unfold_id;
        with_strategy
          transparent [id]
          (assert_succeeds unfold_id;
           with_strategy
             opaque [id]
             (with_strategy
                0 [id]
                (assert_succeeds unfold_id;
                 with_strategy
                   1 [id]
                   (assert_succeeds unfold_id;
                    with_strategy
                    -1 [id]
                       (assert_succeeds unfold_id;
                        with_strategy
                          opaque [id]
                          (assert_fails unfold_id;
                           with_strategy
                             transparent [id]
                             (assert_succeeds unfold_id;
                              with_strategy
                                opaque [id]
                                (with_strategy
                                   expand [id]
                                   (assert_succeeds unfold_id;
                                    let l := strategy_level:(expand) in
                                    with_strategy
                                      l [id]
                                      (let idx := smart_global:(id) in
                                       cbv [idx];
                                       (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
                                       assert_fails
                                         (let idx := smart_global:(id) in
                                          with_strategy
                                            expand [idx]
                                            idtac);
                                       reflexivity)))))))))))).
Qed.
Goal id 0 = 0.
  with_strategy
    opaque [aid]
    (assert_fails unfold_id;
     with_strategy
       transparent [aid]
       (assert_succeeds unfold_id;
        with_strategy
          opaque [aid]
          (with_strategy
             0 [aid]
             (assert_succeeds unfold_id;
              with_strategy
                1 [aid]
                (assert_succeeds unfold_id;
                 with_strategy
                 -1 [aid]
                    (assert_succeeds unfold_id;
                     with_strategy
                       opaque [aid]
                       (assert_fails unfold_id;
                        with_strategy
                          transparent [aid]
                          (assert_succeeds unfold_id;
                           with_strategy
                             opaque [aid]
                             (with_strategy
                                expand [aid]
                                (assert_succeeds unfold_id;
                                 reflexivity)))))))))).
Qed.
Goal id 0 = 0.
  with_strategy
    opaque [idn]
    (assert_fails unfold_id;
     with_strategy
       transparent [idn]
       (assert_succeeds unfold_id;
        with_strategy
          opaque [idn]
          (with_strategy
             0 [idn]
             (assert_succeeds unfold_id;
              with_strategy
                1 [idn]
                (assert_succeeds unfold_id;
                 with_strategy
                 -1 [idn]
                    (assert_succeeds unfold_id;
                     with_strategy
                       opaque [idn]
                       (assert_fails unfold_id;
                        with_strategy
                          transparent [idn]
                          (assert_succeeds unfold_id;
                           with_strategy
                             opaque [idn]
                             (with_strategy
                                expand [idn]
                                (assert_succeeds unfold_id;
                                 reflexivity)))))))))).
Qed.

(* test that strategy tactic does not persist after the execution of the tactic *)
Opaque id.
Goal id 0 = 0.
  assert_fails unfold_id;
    (with_strategy transparent [id] assert_succeeds unfold_id);
    assert_fails unfold_id.
  assert_fails unfold_id.
  with_strategy transparent [id] assert_succeeds unfold_id.
  assert_fails unfold_id.
  reflexivity.
Qed.

(* test that the strategy tactic does persist through abstract *)
Opaque id.
Goal id 0 = 0.
  Time Timeout 5
       with_strategy
       expand [id]
       assert (id (fact 100) = fact 100) by abstract reflexivity.
  reflexivity.
Time Timeout 5 Defined.

(* test that it works even with [Qed] *)
Goal id 0 = 0.
Proof using Type.
  Time Timeout 5
       abstract
       (with_strategy
          expand [id]
          assert (id (fact 100) = fact 100) by abstract reflexivity;
       reflexivity).
Time Timeout 5 Qed.

(* test that the strategy is correctly reverted after closing the goal completely *)
Goal id 0 = 0.
  assert (id 0 = 0) by with_strategy expand [id] reflexivity.
  Fail unfold id.
  reflexivity.
Qed.

(* test that the strategy is correctly reverted after failure *)
Goal id 0 = 0.
  let id' := id in
  (try with_strategy expand [id] fail); assert_fails unfold id'.
  Fail unfold id.
  (* a more complicated test involving a success and then a failure after backtracking *)
  let id' := id in
  ((with_strategy expand [id] (unfold id' + fail)) + idtac);
    lazymatch goal with |- id 0 = 0 => idtac end;
    assert_fails unfold id'.
  Fail unfold id.
  reflexivity.
Qed.

(* test multi-success *)
Goal id (fact 100) = fact 100.
  Timeout 1
          (with_strategy -1 [id] (((idtac + (abstract reflexivity))); fail)).
  Undo.
  Timeout 1
          let id' := id in
          (with_strategy -1 [id] (((idtac + (unfold id'; reflexivity))); fail)).
  Undo.
  Timeout 1
          (with_strategy -1 [id] (idtac + (abstract reflexivity))); fail. (* should not time out *)
  Undo.
  with_strategy -1 [id] abstract reflexivity.
Defined.

(* check that module substitutions happen correctly *)
Module F.
  Definition id {T} := @id T.
  Opaque id.
  Ltac with_transparent_id tac := with_strategy transparent [id] tac.
End F.
Opaque F.id.

Goal F.id 0 = F.id 0.
  Fail unfold F.id.
  F.with_transparent_id ltac:(progress unfold F.id).
  Undo.
  F.with_transparent_id ltac:(let x := constr:(@F.id) in progress unfold x).
Abort.

Module Type Empty. End Empty.
Module E. End E.
Module F2F (E : Empty).
  Definition id {T} := @id T.
  Opaque id.
  Ltac with_transparent_id tac := with_strategy transparent [id] tac.
End F2F.
Module F2 := F2F E.
Opaque F2.id.

Goal F2.id 0 = F2.id 0.
  Fail unfold F2.id.
  F2.with_transparent_id ltac:(progress unfold F2.id).
  Undo.
  F2.with_transparent_id ltac:(let x := constr:(@F2.id) in progress unfold x).
Abort.

(* test the tactic notation entries *)
Tactic Notation "with_strategy0" strategy_level(l) "[" ne_smart_global_list(v) "]" tactic3(tac) := with_strategy l [ v ] tac.
Tactic Notation "with_strategy1" strategy_level_or_var(l) "[" ne_smart_global_list(v) "]" tactic3(tac) := with_strategy l [ v ] tac.
Tactic Notation "with_strategy2" strategy_level(l) "[" constr(v) "]" tactic3(tac) := with_strategy l [ v ] tac.
Tactic Notation "with_strategy3" strategy_level_or_var(l) "[" constr(v) "]" tactic3(tac) := with_strategy l [ v ] tac.

(* [with_strategy0] should work, but it doesn't, due to a combination of https://github.com/coq/coq/issues/11202 and https://github.com/coq/coq/issues/11209 *)
Opaque id.
Goal id 0 = 0.
  Fail (* should work, not Fail *) with_strategy0 opaque [id] idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [id id] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy0 transparent [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [id] idtac.
  Fail (* should work, not Fail *) with_strategy0 0 [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 1 [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 -1 [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [id] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy0 transparent [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [id] idtac.
  Fail (* should work, not Fail *) with_strategy0 expand [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       with_strategy0 expand [idx] idtac.
  reflexivity.
Qed.
Goal id 0 = 0.
  Fail (* should work, not Fail *) with_strategy0 opaque [aid] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy0 transparent [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [aid] idtac.
  Fail (* should work, not Fail *) with_strategy0 0 [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 1 [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 -1 [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [aid] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy0 transparent [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [aid] idtac.
  Fail (* should work, not Fail *) with_strategy0 expand [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  reflexivity.
Qed.
Goal id 0 = 0.
  Fail (* should work, not Fail *) with_strategy0 opaque [idn] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy0 transparent [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [idn] idtac.
  Fail (* should work, not Fail *) with_strategy0 0 [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 1 [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 -1 [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [idn] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy0 transparent [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy0 opaque [idn] idtac.
  Fail (* should work, not Fail *) with_strategy0 expand [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  reflexivity.
Qed.

(* [with_strategy1] should work, but it doesn't, due to a combination of https://github.com/coq/coq/issues/11202 and https://github.com/coq/coq/issues/11209 *)
Opaque id.
Goal id 0 = 0.
  Fail (* should work, not Fail *) with_strategy1 opaque [id] idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [id id] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy1 transparent [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [id] idtac.
  Fail (* should work, not Fail *) with_strategy1 0 [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 1 [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 -1 [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [id] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy1 transparent [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [id] idtac.
  Fail (* should work, not Fail *) with_strategy1 expand [id] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) let l := strategy_level:(expand) in
                                   with_strategy1 l [id] idtac.
  (* This should succeed, but doesn't, basically due to https://github idtac.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       with_strategy1 expand [idx] idtac.
  reflexivity.
Qed.
Goal id 0 = 0.
  Fail (* should work, not Fail *) with_strategy1 opaque [aid] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy1 transparent [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [aid] idtac.
  Fail (* should work, not Fail *) with_strategy1 0 [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 1 [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 -1 [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [aid] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy1 transparent [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [aid] idtac.
  Fail (* should work, not Fail *) with_strategy1 expand [aid] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  reflexivity.
Qed.
Goal id 0 = 0.
  Fail (* should work, not Fail *) with_strategy1 opaque [idn] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy1 transparent [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [idn] idtac.
  Fail (* should work, not Fail *) with_strategy1 0 [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 1 [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 -1 [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [idn] idtac.
  assert_fails unfold_id.
  Fail (* should work, not Fail *) with_strategy1 transparent [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  Fail (* should work, not Fail *) with_strategy1 opaque [idn] idtac.
  Fail (* should work, not Fail *) with_strategy1 expand [idn] idtac.
  Fail (* should work, not Fail *) assert_succeeds unfold_id idtac.
  reflexivity.
Qed.

Opaque id.
Goal id 0 = 0.
  with_strategy2
    opaque [id]
    (with_strategy2
       opaque [id]
       (assert_fails unfold_id;
        with_strategy2
          transparent [id]
          (assert_succeeds unfold_id;
           with_strategy2
             opaque [id]
             (with_strategy2
                0 [id]
                (assert_succeeds unfold_id;
                 with_strategy2
                   1 [id]
                   (assert_succeeds unfold_id;
                    with_strategy2
                    -1 [id]
                       (assert_succeeds unfold_id;
                        with_strategy2
                          opaque [id]
                          (assert_fails unfold_id;
                           with_strategy2
                             transparent [id]
                             (assert_succeeds unfold_id;
                              with_strategy2
                                opaque [id]
                                (with_strategy2
                                   expand [id]
                                   (assert_succeeds unfold_id))))))))))).
  (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       with_strategy2 expand [idx] idtac.
  reflexivity.
Qed.
Goal id 0 = 0.
  with_strategy2
    opaque [aid]
    (with_strategy2
       opaque [aid]
       (assert_fails unfold_id;
        with_strategy2
          transparent [aid]
          (assert_succeeds unfold_id;
           with_strategy2
             opaque [aid]
             (with_strategy2
                0 [aid]
                (assert_succeeds unfold_id;
                 with_strategy2
                   1 [aid]
                   (assert_succeeds unfold_id;
                    with_strategy2
                    -1 [aid]
                       (assert_succeeds unfold_id;
                        with_strategy2
                          opaque [aid]
                          (assert_fails unfold_id;
                           with_strategy2
                             transparent [aid]
                             (assert_succeeds unfold_id;
                              with_strategy2
                                opaque [aid]
                                (with_strategy2
                                   expand [aid]
                                   (assert_succeeds unfold_id))))))))))).
  reflexivity.
Qed.
Goal id 0 = 0.
  with_strategy2
    opaque [idn]
    (with_strategy2
       opaque [idn]
       (assert_fails unfold_id;
        with_strategy2
          transparent [idn]
          (assert_succeeds unfold_id;
           with_strategy2
             opaque [idn]
             (with_strategy2
                0 [idn]
                (assert_succeeds unfold_id;
                 with_strategy2
                   1 [idn]
                   (assert_succeeds unfold_id;
                    with_strategy2
                    -1 [idn]
                       (assert_succeeds unfold_id;
                        with_strategy2
                          opaque [idn]
                          (assert_fails unfold_id;
                           with_strategy2
                             transparent [idn]
                             (assert_succeeds unfold_id;
                              with_strategy2
                                opaque [idn]
                                (with_strategy2
                                   expand [idn]
                                   (assert_succeeds unfold_id))))))))))).
  reflexivity.
Qed.

Opaque id.
Goal id 0 = 0.
  with_strategy3
    opaque [id]
    (with_strategy3
       opaque [id]
       (assert_fails unfold_id;
        with_strategy3
          transparent [id]
          (assert_succeeds unfold_id;
           with_strategy3
             opaque [id]
             (with_strategy3
                0 [id]
                (assert_succeeds unfold_id;
                 with_strategy3
                   1 [id]
                   (assert_succeeds unfold_id;
                    with_strategy3
                    -1 [id]
                       (assert_succeeds unfold_id;
                        with_strategy3
                          opaque [id]
                          (assert_fails unfold_id;
                           with_strategy3
                             transparent [id]
                             (assert_succeeds unfold_id;
                              with_strategy3
                                opaque [id]
                                (with_strategy3
                                   expand [id]
                                   (assert_succeeds unfold_id))))))))))).
  (* This should succeed, but doesn't, basically due to https://github.com/coq/coq/issues/11202 *)
  Fail let idx := smart_global:(id) in
       with_strategy3 expand [idx] idtac.
  reflexivity.
Qed.
Goal id 0 = 0.
  with_strategy3
    opaque [aid]
    (with_strategy3
       opaque [aid]
       (assert_fails unfold_id;
        with_strategy3
          transparent [aid]
          (assert_succeeds unfold_id;
           with_strategy3
             opaque [aid]
             (with_strategy3
                0 [aid]
                (assert_succeeds unfold_id;
                 with_strategy3
                   1 [aid]
                   (assert_succeeds unfold_id;
                    with_strategy3
                    -1 [aid]
                       (assert_succeeds unfold_id;
                        with_strategy3
                          opaque [aid]
                          (assert_fails unfold_id;
                           with_strategy3
                             transparent [aid]
                             (assert_succeeds unfold_id;
                              with_strategy3
                                opaque [aid]
                                (with_strategy3
                                   expand [aid]
                                   (assert_succeeds unfold_id))))))))))).
  reflexivity.
Qed.
Goal id 0 = 0.
  with_strategy3
    opaque [idn]
    (with_strategy3
       opaque [idn]
       (assert_fails unfold_id;
        with_strategy3
          transparent [idn]
          (assert_succeeds unfold_id;
           with_strategy3
             opaque [idn]
             (with_strategy3
                0 [idn]
                (assert_succeeds unfold_id;
                 with_strategy3
                   1 [idn]
                   (assert_succeeds unfold_id;
                    with_strategy3
                    -1 [idn]
                       (assert_succeeds unfold_id;
                        with_strategy3
                          opaque [idn]
                          (assert_fails unfold_id;
                           with_strategy3
                             transparent [idn]
                             (assert_succeeds unfold_id;
                              with_strategy3
                                opaque [idn]
                                (with_strategy3
                                   expand [idn]
                                   (assert_succeeds unfold_id))))))))))).
  reflexivity.
Qed.

(* Fake out coqchk to work around what is essentially COQBUG(https://github.com/coq/coq/issues/12200) *)
Reset Initial.
