- **Changed:**
  signal `SIGINT` interrupts the process with " "user interrupt" error
  instead of aborting. This is intended to produce better messages when interrupting Coq
  (`#18716 <https://github.com/coq/coq/pull/18716>`_,
  by Gaëtan Gilbert).
