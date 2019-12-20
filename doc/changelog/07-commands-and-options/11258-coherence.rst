- **Changed:**
  The :cmd:`Coercion` command has been improved to check the coherence of the
  inheritance graph. It checks whether a circular inheritance path of `C >-> C`
  is convertible with the identity function or not, then report it as an
  ambiguous path if it is not.  The new mechanism does not report ambiguous
  paths that are redundant with others. For example, checking the ambiguity of
  `[f; g]` and `[f'; g]` is redundant with that of `[f]` and `[f']` thus will
  not be reported
  (`#11258 <https://github.com/coq/coq/pull/11258>`_,
  by Kazuhiko Sakaguchi).
