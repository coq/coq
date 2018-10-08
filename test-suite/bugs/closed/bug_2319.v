Section S.

  CoInductive A (X: Type) := mkA: A X -> A X.
  Variable T : Type.

  (* This used to loop (bug #2319) *)
  Timeout 5 Eval vm_compute in cofix s : A T := mkA T s.

  CoFixpoint s : A T := mkA T s
        with t : A unit := mkA unit (mkA unit t).
  Timeout 5 Eval vm_compute in s.

End S.
