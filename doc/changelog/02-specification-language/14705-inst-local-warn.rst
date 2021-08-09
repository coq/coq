- **Changed:**
  :cmd:`Instance` warns about the default locality immediately rather than waiting until the instance is ready to be defined.
  This changes which command warns when the instance has a separate proof: the :cmd:`Instance` command itself warns instead of the proof closing command (such as :cmd:`Defined`).
  (`#14705 <https://github.com/coq/coq/pull/14705>`_,
  by Gaëtan Gilbert).
