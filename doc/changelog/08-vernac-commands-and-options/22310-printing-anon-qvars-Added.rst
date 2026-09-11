- **Added:**
  flag ``Printing Unnamed Universes Anonymously``, which prints
  universe levels and sort quality variables that cannot be referred
  to by name as ``_`` (which can be parsed back, denoting a fresh
  level or quality variable) instead of their raw forms such as
  ``Lib.23`` or ``α3`` (which cannot); a sort whose universe is a
  ``max`` with such a level prints as ``Type@{_}``
  (`#22310 <https://github.com/rocq-prover/rocq/pull/22310>`_,
  written by Claude (Anthropic), for Jason Gross).
