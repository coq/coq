- The tactic :tacn:`rapply` in :g:`Coq.Program.Tactics` now handles
  arbitrary numbers of underscores and takes in a :g:`uconstr`.  In
  rare cases where users were relying on :tacn:`rapply` inserting
  exactly 15 underscores and no more, due to the lemma having a
  completely unspecified codomain (and thus allowing for any number of
  underscores), the tactic will now instead loop.  Additional
  incompatibility may occur in cases where it was important to
  interpret the lemma passed in to :tacn:`rapply` as a :g:`constr`
  (thus failing on unresolved holes and resolving typeclasses before
  adding arguments) before refining with it.  Users may work around
  this by replacing all invocations of :tacn:`rapply` with the
  qualified :g:`Tactics.rapply` to get the underlying tactic rather
  than the tactic notation.  Finally, any users who defined their own
  tactic :tacn:`rapply` and also imported :g:`Coq.Program.Tactics` may
  see incompatibilities due to the fact that :g:`Coq.Program.Tactics`
  now defines an :tacn:`rapply` as a :cmd:`Tactic Notation`.  Users
  can work around this by defining their :tacn:`rapply` as a
  :cmd:`Tactic Notation` as well. (`#10760
  <https://github.com/coq/coq/pull/10760>`_, by Jason Gross)
