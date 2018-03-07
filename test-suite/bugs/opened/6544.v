Hint Resolve plus_n_O | 0 (?X = ?X + 0).
Hint Extern 0 (?X = ?X + 0) => simple apply plus_n_O.

Goal forall n, n = n + (0 + 0).
  intros n.
  solve [auto].
  Undo.
  solve [eauto].          (* can be solved because we have `plus_n_O` hint *)
  Undo.
  Remove Hints plus_n_O : core.
  Fail solve [auto].
  Fail solve [eauto].     (* fails as expected *)
  Hint Extern 0 (?X = ?X + 0) => simple apply plus_n_O.
  Fail solve [auto].
  Fail solve [eauto].     (* I'd expect this to work, since the following works *)
  Hint Resolve plus_n_O | 0 (?X = ?X + 0).
  solve [auto].
  Undo.
  solve [eauto].
Qed.
