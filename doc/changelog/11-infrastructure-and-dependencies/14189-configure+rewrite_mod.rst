- **Changed:**
  Coq's ``./configure`` script has gone through a major cleanup. In
  particular, the following options have been removed:
  - ``-force-caml-version``, ``-force-findlib-version``: Coq won't
  compile with OCaml or findlib lower than the required versions;
  - ``-vmbyteflags``, ``-custom``, ``-no-custom``: linking options for
  toplevels are now controlled in ``topbin/dune``;
  - ``-ocamlfind``: Coq will now use the toolchain specified in the
  Dune configuration; this can be controlled using the workspaces
  feature;
  - ``-nodebug``: Coq will now follow the standard, which is to always
  pass ``-g`` to OCaml; this can be modified using a custom Dune workspace;
  - ``-flambda-opts``: compilation options are now set in Coq's root
  ``dune`` file, can be updated using a custom Dune workspace;
  - ``-local``, ``-bindir``, ``-coqdocdir``, ``-annotate``,
  ``-camldir``, ``-profiling``: these flags were deprecated in 8.14,
  and are now removed.
  Moreover, the ``-annot`` and ``-bin-annot`` flags only take effect
  to set ``coq-makefile``'s defaults.
  (`#14189 <https://github.com/coq/coq/pull/14189>`_,
  by Emilio Jesus Gallego Arias).
