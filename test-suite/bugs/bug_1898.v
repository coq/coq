(* folding should not allow circular dependencies *)

Lemma bug_fold_unfold : True.
  set (h := 1).
  Fail fold h in h.
  Abort.
