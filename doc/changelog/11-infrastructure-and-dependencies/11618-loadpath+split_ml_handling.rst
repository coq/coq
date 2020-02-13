- **Changed:**
  Recursive OCaml loadpaths are not supported anymore; the command
  ``Add Rec ML Path`` has been removed; :cmd:`Add ML Path` is now the
  preferred one. We have also dropped support for the non-qualified
  version of the :cmd:`Add LoadPath` command, that is to say,
  the ``Add LoadPath dir`` version; now,
  you must always specify a prefix now using ``Add Loadpath dir as Prefix.``
  (`#11618 <https://github.com/coq/coq/pull/11618>`_,
  by Emilio Jesus Gallego Arias).
