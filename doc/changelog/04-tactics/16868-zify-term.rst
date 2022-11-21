- **Added:** :cmd:`Add Zify` now accepts terms instead of only references.
  This lets you avoid creating intermediate definitions for terms
  that include section variables (such as ``x`` in ``(inj_thing x)``).
  Now you can use ``Add Zify InjTyp (inj_thing x)`` instead (`#16868
  <https://github.com/coq/coq/pull/16868>`_, by Gaëtan Gilbert).
