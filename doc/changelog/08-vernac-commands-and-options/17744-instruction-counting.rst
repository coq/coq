- **Added:**
  new command modifier :cmd:`Instructions` that executes the given command and
  displays the number of CPU instructions it took to execute it. This command
  is currently only supported on Linux systems, but it does not fail on other
  systems, where it simply shows an error message instead of the count.
  (`#17744 <https://github.com/coq/coq/pull/17744>`_,
  by Rodolphe Lepigre).
- **Added:**
  support for instruction counts to the `-profile` option.
  (`#17744 <https://github.com/coq/coq/pull/17744>`_,
  by Rodolphe Lepigre).
