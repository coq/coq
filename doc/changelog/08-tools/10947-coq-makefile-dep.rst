- Renamed `VDFILE` from `.coqdeps.d` to `.<CoqMakefile>.d` in the `coq_makefile`
  utility, where `<CoqMakefile>` is the name of the output file given by the
  `-o` option. In this way two generated makefiles can coexist in the same
  directory.
  (`#10947 <https://github.com/coq/coq/pull/10947>`_, by Kazuhiko Sakaguchi).
