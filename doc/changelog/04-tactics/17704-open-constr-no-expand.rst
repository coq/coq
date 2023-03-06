- **Changed:**
  `open_constr` in Ltac1 and Ltac2 does not perform evar normalization.
  Normalization may be recovered using `let c := open_constr:(...) in constr:(c)`
  if necessary for performance
  (`#17704 <https://github.com/coq/coq/pull/17704>`_,
  by Gaëtan Gilbert).
