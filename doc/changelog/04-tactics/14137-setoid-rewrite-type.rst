- **Added:**
  generalized rewriting now supports rewriting with (possibly polymorphic)
  relations valued in ``Type``. Use ``Classes.CMorphisms`` instead of
  ``Classes.Morphisms`` to declare ``Proper`` instances for :tacn:`rewrite`
  (or :tacn:`setoid_rewrite`) to use when rewriting with ``Type`` valued
  relations.
  (`#14137 <https://github.com/coq/coq/pull/14137>`_,
  fixes `#4632 <https://github.com/coq/coq/issues/4632>`_
  and `#5384 <https://github.com/coq/coq/issues/5384>`_
  and `#5521 <https://github.com/coq/coq/issues/5521>`_
  and `#6278 <https://github.com/coq/coq/issues/6278>`_
  and `#7675 <https://github.com/coq/coq/issues/7675>`_
  and `#8739 <https://github.com/coq/coq/issues/8739>`_
  and `#11011 <https://github.com/coq/coq/issues/11011>`_
  and `#12240 <https://github.com/coq/coq/issues/12240>`_
  and `#15279 <https://github.com/coq/coq/issues/15279>`_,
  by Matthieu Sozeau helped by Ali Caglayan).
