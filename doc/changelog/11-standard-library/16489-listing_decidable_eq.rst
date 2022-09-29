- **Added:**
  three lemmata related to finiteness and decidability of equality:
  :g:`Listing_decidable_eq`, :g:`Finite_dec`
  to ``FinFun.v`` and lemma :g:`NoDup_list_decidable` to ``ListDec.v``
  (`#16489 <https://github.com/coq/coq/pull/16489>`_,
  fixes `#16479 <https://github.com/coq/coq/issues/16479>`_,
  by Bodo Igler, with help from Olivier Laurent and Andrej Dudenhefner).

- **Deprecated:**
  lemma :g:`Finite_alt` in ``FinFun.v``, which is a weaker version of
  the newly added lemma :g:`Finite_dec`
  (`#16489 <https://github.com/coq/coq/pull/16489>`_,
  fixes `#16479 <https://github.com/coq/coq/issues/16479>`_,
  by Bodo Igler, with help from Olivier Laurent).
