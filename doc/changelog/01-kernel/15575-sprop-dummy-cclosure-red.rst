- **Fixed:**
  We introduce a new irrelevant term in the reduction machine.
  It is used to shortcut computation of terms living in a strict
  proposition, and behaves as an exception. This restores subject
  reduction, and also makes conversion of large terms in SProp
  cheap
  (`#15575 <https://github.com/coq/coq/pull/15575>`_,
  fixes `#14015 <https://github.com/coq/coq/issues/14015>`_,
  by Pierre-Marie Pédrot).
