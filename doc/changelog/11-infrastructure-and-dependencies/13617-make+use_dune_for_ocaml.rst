- **Changed:**
  Coq's OCaml parts and tools [coq-core] are now built using Dune.
  The main user-facing change is that Dune >= 2.5 is now required to
  build Coq, most recent Dune is usually recommended.
  For developers and plugin authors, see the entry in
  `dev/doc/changes.md`.
  (`#13617 <https://github.com/coq/coq/pull/13617>`_,
  by Emilio Jesus Gallego Arias and Théo Zimmerman; review and testing by
  Gaëtan Gilbert, Guillaume Melquiond, and Enrico Tassi)
