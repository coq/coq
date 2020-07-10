- **Fixed:**
  A loss of definitional equality for declarations obtained through
  :cmd:`Include` when entering the scope of a :cmd:`Module` or
  :cmd:`Module Type` was causing :cmd:`Search` not to see the included
  declarations
  (`#12537 <https://github.com/coq/coq/pull/12537>`_, fixes `#12525
  <https://github.com/coq/coq/pull/12525>`_ and `#12647
  <https://github.com/coq/coq/pull/12647>`_, by Hugo Herbelin).
