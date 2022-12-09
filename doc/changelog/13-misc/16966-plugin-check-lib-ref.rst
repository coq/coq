- **Added:**
  warning `dynlink-name-lookup` when a plugin looks up a reference at linking time.
  Such lookups are the most common cause of incompatibility with asynchronous proofs
  (`#16966 <https://github.com/coq/coq/pull/16966>`_,
  by Gaëtan Gilbert).
