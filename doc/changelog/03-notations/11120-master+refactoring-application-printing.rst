- **Fixed:** Inheritance of implicit arguments across notations made
  uniform in parsing and printing. To the exception of notations of
  the form ``Notation "..." := @foo`` and ``Notation id := @foo`` which
  inhibit implicit arguments, all notations binding a partially
  applied constant, as e.g. in ``Notation "..." := (foo args)``,
  or ``Notation "..." := (@foo args)``, or ``Notation id := (foo args)``, or
  ``Notation id := (@foo args)``, inherits the remaining implicit arguments
  (`#11120 <https://github.com/coq/coq/pull/11120>`_, by Hugo
  Herbelin, fixing `#4690 <https://github.com/coq/coq/pull/4690>`_ and
  `#11091 <https://github.com/coq/coq/pull/11091>`_).

- **Changed:** Interpretation scopes are now always inherited in
  notations binding a partially applied constant, including for
  notations binding an expression of the form ``@foo``. The latter was
  not the case beforehand
  (part of `#11120 <https://github.com/coq/coq/pull/11120>`_).
