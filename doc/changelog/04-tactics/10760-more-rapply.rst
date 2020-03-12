- **Changed:**
  The tactic :tacn:`rapply` in :g:`Coq.Program.Tactics` now handles
  arbitrary numbers of underscores and takes in a :g:`uconstr`.  In
  rare cases where users were relying on :tacn:`rapply` inserting
  exactly 15 underscores and no more, due to the lemma having a
  completely unspecified codomain (and thus allowing for any number of
  underscores), the tactic will now instead loop (`#10760
  <https://github.com/coq/coq/pull/10760>`_, by Jason Gross).
