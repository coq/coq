- **Changed:**
  ``Require Import Coq.nsatz.NsatzTactic`` now allows using :tacn:`nsatz`
  with `Z` and `Q` without having to supply instances or using ``Require Import Coq.nsatz.Nsatz``, which
  transitively requires unneeded files declaring axioms used in the reals
  (`#12861 <https://github.com/coq/coq/pull/12861>`_,
  fixes `#12860 <https://github.com/coq/coq/issues/12860>`_,
  by Jason Gross).
