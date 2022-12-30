- **Changed:**
  Do not pass the ``-rectypes`` flag by default in
  ``coq_makefile`` when compiling OCaml code, since
  it is no longer required by Coq. To re-enable passing
  the flag, put ``CAMLFLAGS+=-rectypes`` in the local makefile,
  e.g., ``CoqMakefile.local`` (see :ref:`coqmakefilelocal`)
  (`#17038 <https://github.com/coq/coq/pull/17038>`_,
  by Karl Palmskog with help from Gaëtan Gilbert).
