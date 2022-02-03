- **Changed:**
  Load plugins using `findlib <http://projects.camlcity.org/projects/findlib.html>`_.
  This requires projects built with ``coq_makefile`` to either provide a
  hand written ``META`` file or use the ``-generate-meta-for-package`` option
  when applicable. As a consequence :cmd:`Declare ML Module` now uses plugin
  names according to ``findlib``, e.g. `coq-aac-tactics.plugin`.
  ``coqdep`` accepts ``-m META`` and use the file to resolve plugin names to
  actual file names.
  (`#15220 <https://github.com/coq/coq/pull/15220>`_,
  fixes `#7698 <https://github.com/coq/coq/issues/7698>`_,
  by Enrico Tassi).
