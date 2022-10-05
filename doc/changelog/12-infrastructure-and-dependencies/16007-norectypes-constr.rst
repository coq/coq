- **Changed:**
  Coq is not compiled with OCaml's ``-rectypes`` option anymore.
  This means plugins which do not exploit it can also stop passing it to OCaml
  (`#16007 <https://github.com/coq/coq/pull/16007>`_,
  by Gaëtan Gilbert).
