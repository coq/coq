- **Changed:**
  Warn when manual implicit arguments are used in unexpected positions
  of a term (e.g. in `Check id (forall {x}, x)`) or when a implicit
  argument name is shadowed (e.g. in `Check fun f : forall {x:nat}
  {x}, nat => f`)
  (`#10202 <https://github.com/coq/coq/pull/10202>`_,
  by Hugo Herbelin).
