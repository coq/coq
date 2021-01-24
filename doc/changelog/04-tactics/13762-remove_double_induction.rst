- **Removed:**
  double induction tactic.  Replace :n:`double induction @ident @ident`
  with :n:`induction @ident; induction @ident` (or
  :n:`induction @ident ; destruct @ident` depending on the exact needs).
  Replace :n:`double induction @natural__1 @natural__2` with
  :n:`induction @natural__1; induction natural__3` where :n:`natural__3` is the result
  of :n:`natural__2 - natural__1`
  (`#13762 <https://github.com/coq/coq/pull/13762>`_,
  by Jim Fehrle).
