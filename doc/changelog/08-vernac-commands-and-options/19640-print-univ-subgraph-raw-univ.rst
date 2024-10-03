- **Added:**
  :cmd:`Print Universes` `Subgraph` accepts raw universe names (which end in an integer instead of an identifier)
  for debugging purposes, eg `Print Universes Subgraph ("foo.1" "foo.2")`.
  The integer in raw universe expressions is extremely unstable,
  so raw universe expressions should not be used outside debugging sessions
  (`#19640 <https://github.com/coq/coq/pull/19640>`_,
  by Gaëtan Gilbert).
