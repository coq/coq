- **Fixed:** Inheritance of implicit arguments across notations made
  uniform in parsing and printing. To the exception of notations of
  the form :n:`Notation @string := @@qualid` and :n:`Notation @ident := @@qualid` which
  inhibit implicit arguments, all notations binding a partially
  applied constant, as e.g. in :n:`Notation @string := (@qualid {+ @arg })`,
  or :n:`Notation @string := (@@qualid {+ @arg })`, or
  :n:`Notation @ident := (@qualid {+ @arg })`, or :n:`Notation @ident
  := (@@qualid {+ @arg })`, inherit the remaining implicit arguments
  (`#11120 <https://github.com/coq/coq/pull/11120>`_, by Hugo
  Herbelin, fixing `#4690 <https://github.com/coq/coq/pull/4690>`_ and
  `#11091 <https://github.com/coq/coq/pull/11091>`_).

- **Changed:** Interpretation scopes are now always inherited in
  notations binding a partially applied constant, including for
  notations binding an expression of the form :n:`@@qualid`. The latter was
  not the case beforehand
  (part of `#11120 <https://github.com/coq/coq/pull/11120>`_).
