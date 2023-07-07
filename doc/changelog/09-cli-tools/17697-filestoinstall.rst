- **Fixed:**
  `coq_makefile` avoids generating a command containing all files to install in a make rule,
  which could surpass the maximum single argument size in some developments
  (`#17697 <https://github.com/coq/coq/pull/17697>`_,
  fixes `#17721 <https://github.com/coq/coq/issues/17721>`_,
  by Gaëtan Gilbert).
