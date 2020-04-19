- **Changed:**
  It is now possible to import the :g:`nsatz` machinery without
  transitively depending on the axioms of the real numbers nor of
  classical logic by loading ``Coq.nsatz.NsatzTactic`` rather than
  ``Coq.nsatz.Nsatz``.  Note that some constants have changed kernel
  names, living in ``Coq.nsatz.NsatzTactic`` rather than
  ``Coq.nsatz.Nsatz``; this might cause minor incompatibilities that
  can be fixed by actually running :g:`Import Nsatz` rather than
  relying on absolute names (fixes `#5445
  <https://github.com/coq/coq/issues/5445>`_, `#12073
  <https://github.com/coq/coq/pull/12073>`_, by Jason Gross).
