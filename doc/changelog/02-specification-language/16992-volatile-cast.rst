- **Added:**
  volatile casts :n:`@term :> @type` which do not leave a trace in the elaborated term.
  They are used by :flag:`Printing Match All Subterms` to display otherwise hidden subterms of match constructs
  (`#16992 <https://github.com/coq/coq/pull/16992>`_,
  fixes `#16918 <https://github.com/coq/coq/issues/16918>`_,
  by Gaëtan Gilbert).
