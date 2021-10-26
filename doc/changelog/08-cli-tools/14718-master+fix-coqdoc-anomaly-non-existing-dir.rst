- **Changed:**
  :cmd:`Require` now selects files whose logical name
  exactly matches the required name, making it possible to unambiguously select
  a given file: if several :n:`-Q` or :n:`-R` options bind the same
  logical name to a different file, the option appearing last on the
  command line takes precedence.  Moreover, it is now an error to
  require a file using a partial logical name which does not resolve
  to a non-ambiguous path (`#14718
  <https://github.com/coq/coq/pull/14718>`_, by Hugo Herbelin).

- **Fixed:**
  Various `coqdep` issues with the `From` clause of :cmd:`Require` and
  a few inconsistencies between `coqdep` and `coqc` disambiguation
  of :cmd:`Require`
  (`#14718 <https://github.com/coq/coq/pull/14718>`_,
  fixes `#11631 <https://github.com/coq/coq/issues/11631>`_
  and `#14539 <https://github.com/coq/coq/issues/14539>`_,
  by Hugo Herbelin).
