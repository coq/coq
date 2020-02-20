- **Changed:**
  Internal options and behavior of ``coqdep`` have changed. ``coqdep``
  no longer works as a replacement for ``ocamldep``, thus ``.ml``
  files are not supported as input. Also, several deprecated options
  have been removed: ``-w``, ``-D``, ``-mldep``, ``-prefix``,
  ``-slash``, and ``-dumpbox``. Passing ``-boot`` to ``coqdep`` will
  not load any path by default now, ``-R/-Q`` should be used instead.
  (`#11523 <https://github.com/coq/coq/pull/11523>`_ and
  `#11589 <https://github.com/coq/coq/pull/11589>`_,
  by Emilio Jesus Gallego Arias).
