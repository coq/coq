- **Fixed:**
  the kernel now checks that case elimination of private inductive types (cf :attr:`private(matching)`) is not used outside their defining module.
  Previously this was only checked in elaboration and the check could be avoided through some tactics, breaking consistency in the presence of axioms which rely on the elimination restriction to be consistent.
  (`#17452 <https://github.com/coq/coq/pull/17452>`_,
  fixes `#9608 <https://github.com/coq/coq/issues/9608>`_,
  by Gaëtan Gilbert).
