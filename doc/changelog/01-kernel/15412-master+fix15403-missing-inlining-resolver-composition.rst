- **Fixed:**
  Inlining of non-logical objects (notations, hints, ...) was missing
  when applying a functor returning one of its arguments as e.g. in
  :n:`Module F (E:T) := E`
  (`#15412 <https://github.com/coq/coq/pull/15412>`_,
  fixes `#15403 <https://github.com/coq/coq/issues/15403>`_,
  by Hugo Herbelin).
