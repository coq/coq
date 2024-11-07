- **Changed:**
  When unification fails to instantiate an evar because
  of a problem that occurs under a beta-redex, we reduce
  this beta-redex and try again
  (`#19833 <https://github.com/coq/coq/pull/19833>`_,
  by Quentin Vermande).
