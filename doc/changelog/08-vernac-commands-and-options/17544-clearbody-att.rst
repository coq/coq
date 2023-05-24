- **Added:**
  :attr:`clearbody` for :cmd:`Let` to clear the body of a let-in in an interactive
  proof without kernel enforcement.  (This is the behavior that was previously
  provided by using :cmd:`Qed`, which is now deprecated for `Let`\s.)
  (`#17544 <https://github.com/coq/coq/pull/17544>`_,
  by Gaëtan Gilbert).
- **Deprecated:**
  Using :cmd:`Qed` with :cmd:`Let`. End the proof with :cmd:`Defined` and use :attr:`clearbody`
  instead to get the same behavior
  (`#17544 <https://github.com/coq/coq/pull/17544>`_,
  by Gaëtan Gilbert).
