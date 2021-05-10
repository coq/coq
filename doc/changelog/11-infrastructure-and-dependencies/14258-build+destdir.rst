- **Changed:**
  Undocumented variables ``OLDROOT`` and ``COQPREFIXINSTALL`` which
  added a prefix path to `make install`have been removed. Now, ``make
  install`` does support the more standard ``DESTDIR`` variable, akin
  to what ``coq_makefile`` does.
  (`#14258 <https://github.com/coq/coq/pull/14258>`_,
  by Emilio Jesus Gallego Arias).
