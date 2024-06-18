- **Removed:**
  the kernel always produces an error when given terms with bad relevances
  instead of emitting the default-error `bad-relevance` warning
  (which is now only used by the higher layers)
  (`#19164 <https://github.com/coq/coq/pull/19164>`_,
  by Gaëtan Gilbert).
