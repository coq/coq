- **Fixed:**
  unification is less sensitive to whether a subterm is
  an indirection through a defined existential variable or a direct term node.
  This results in less constant unfoldings in rare cases
  (`#16960 <https://github.com/coq/coq/pull/16960>`_,
  by Gaëtan Gilbert).
