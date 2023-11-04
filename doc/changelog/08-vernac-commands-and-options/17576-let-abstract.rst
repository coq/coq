- **Changed:**
  :cmd:`Let` with :cmd:`Qed` produces an opaque side definition
  instead of being treated as a transparent `let` after the section is closed.
  The previous behaviour can be recovered using :attr:`clearbody` and :cmd:`Defined`
  (`#17576 <https://github.com/coq/coq/pull/17576>`_,
  by Gaëtan Gilbert).
