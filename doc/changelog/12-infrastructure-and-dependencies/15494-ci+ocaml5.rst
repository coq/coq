- **Added:**
  Coq now supports OCaml 5; note that OCaml 5 is not compatible with
  Coq's native reduction machine, so Coq's ``configure`` will fail in
  this case unless the ``-native-compiler no`` option is used. Note
  that ``configure``'s default is ``-native-compile ondemand`` so if
  you were relying on the default you'll have to disable the native
  machinery explicitly now
  (`#15494 <https://github.com/coq/coq/pull/15494>`_,
  by Emilio Jesus Gallego Arias, Gaëtan Gilbert, Guillaume Melquiond,
  Pierre-Marie Pédrot, and others).
