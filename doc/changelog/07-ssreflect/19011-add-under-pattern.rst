- **Added:**
  Contextual pattern ``UNDER``, which restricts the scope
  of :tacn:`rewrite <rewrite (ssreflect)>` to the current :tacn:`under` context.
  This pattern is useful to work around the issue that occurs when rewriting an
  equality directly involving the main bound variable.
  Now you can write: :g:`rewrite [UNDER]lem.`, or :g:`rewrite [in UNDER]lem.`
  (`#19011 <https://github.com/coq/coq/pull/19011>`_,
  workaround for `#11118 <https://github.com/coq/coq/issues/11118>`_,
  by Erik Martin-Dorel).
