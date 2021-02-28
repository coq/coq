- **Changed:**
  Native-code libraries used by :tacn:`native_compute` are now delayed
  until an actual call to the :tacn:`native_compute` machinery is
  performed. This should make Coq more responsive on some systems
  (`#13853 <https://github.com/coq/coq/pull/13853>`_, fixes `#13849
  <https://github.com/coq/coq/issues/13849>`_, by Guillaume Melquiond).
