- **Changed:**
  The output of ``make TIMED=1`` (and therefore the timing targets
  such as ``print-pretty-timed`` and ``print-pretty-timed-diff``) now
  displays the full name of the output file being built, rather than
  the stem of the rule (which was usually the filename without the
  extension, but in general could be anything for user-defined rules
  involving ``%``) (`#12126
  <https://github.com/coq/coq/pull/12126>`_, by Jason Gross).
