- **Fixed:**
  The name of a cofixpoint globally defined with a name is now
  systematically reused by :tacn:`simpl` after reduction, even when
  the named cofixpoint is mutually defined or defined in a section
  (`#18576 <https://github.com/coq/coq/pull/18576>`_,
  fixes `#4056 <https://github.com/coq/coq/issues/4056>`_,
  by Hugo Herbelin).
