- **Fixed:**
  Wrong type error in tactic :tacn:`functional induction`.
  (`#12326 <https://github.com/coq/coq/pull/12326>`_,
  by Pierre Courtieu,
  fixes `#11761 <https://github.com/coq/coq/issues/11761>`_,
  reported by Lasse Blaauwbroek).
- **Changed**
  When the tactic :tacn:`functional induction` :n:`c__1 c__2 ... c__n` is used
  with no parenthesis around :n:`c__1 c__2 ... c__n`, :n:`c__1 c__2 ... c__n` is now
  read as one sinlge applicative term. In particular implicit
  arguments should be omitted. Rare source of incompatibility
  (`#12326 <https://github.com/coq/coq/pull/12326>`_,
  by Pierre Courtieu).
