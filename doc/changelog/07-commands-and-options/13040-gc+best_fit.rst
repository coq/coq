- **Changed:**
  When compiled with OCaml >= 4.10.0, Coq will use the new best-fit GC
  policy, which should provide some performance benefits. Coq's policy
  is optimized for speed, but could increase memory consumption in
  some cases. You are welcome to tune it using the ``OCAMLRUNPARAM``
  variable and report back setting so we could optimize more.
  (`#13040 <https://github.com/coq/coq/pull/13040>`_,
  fixes `#11277 <https://github.com/coq/coq/issues/11277>`_,
  by Emilio Jesus Gallego Arias).
