- **Changed:**
  Coq's core system now uses the `zarith <https://github.com/ocaml/Zarith>`_
  library, based on GNU's gmp instead of ``num`` which is
  deprecated upstream. The custom ``bigint`` module is
  not longer provided; note that the ``micromega`` still uses
  ``num``
  (`#11742 <https://github.com/coq/coq/pull/11742>`_,
  by Emilio Jesus Gallego Arias and Vicent Laporte).
