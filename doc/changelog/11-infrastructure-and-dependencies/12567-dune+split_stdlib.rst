- **Changed:**
  Coq's configure script now requires absolute paths for the `-prefix`
  option.
  (`#12567 <https://github.com/coq/coq/pull/12567>`_,
  by Emilio Jesus Gallego Arias).

- **Changed:**
  The regular Coq package has been split in two: coq-core, with
  OCaml-based libraries and tools; and coq-stdlib, which contains the
  Gallina-based standard library. The package Coq now depends on both
  for compatiblity.
  (`#12567 <https://github.com/coq/coq/pull/12567>`_,
  by Emilio Jesus Gallego Arias, review by Vincent Laporte, Guillaume
  Melquiond, Enrico Tassi, and Théo Zimmerman).
