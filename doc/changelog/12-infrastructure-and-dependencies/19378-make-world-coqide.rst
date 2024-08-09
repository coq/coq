- **Changed:**
  when building Coq, the makefile's `world` target and `dune build`'s default target do not build coqide anymore.
  Use `make world coqide` or `dune build @default coqide.install` to build what they respectively used to build
  (`#19378 <https://github.com/coq/coq/pull/19378>`_,
  by Gaëtan Gilbert).
