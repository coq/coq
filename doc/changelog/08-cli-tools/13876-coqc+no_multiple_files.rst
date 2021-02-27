- **Changed:**
  `coqc` now enforces that at most a single `.v` file can be passed in
  the command line. Support for multiple `.v` files in the form of
  `coqc f1.v f2.v` didn't properly work in 8.13, tho it was accepted.
  (`#13876 <https://github.com/coq/coq/pull/13876>`_,
  by Emilio Jesus Gallego Arias).
