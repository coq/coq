- **Changed:**
  extensions to the term syntax through generic arguments (typically `ltac:()`, `ltac2:()` or ltac2's `$`)
  produce errors when used in term patterns (for instance patterns used to filter hints) instead of being treated as holes (`_`)
  (`#17352 <https://github.com/coq/coq/pull/17352>`_,
  by Gaëtan Gilbert).
