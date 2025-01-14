- **Changed:**
  when building Coq, the makefile's `world` target and `dune build`'s default target do not build rocqide anymore.
  Use `make world rocqide` or `dune build @default rocqide.install` to build what they respectively used to build
  (`#19378 <https://github.com/coq/coq/pull/19378>`_,
  by Gaëtan Gilbert).
