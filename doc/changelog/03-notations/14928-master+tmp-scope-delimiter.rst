- **Added:**
  the notation :g:`term%_scope` to set a scope only temporarily
  (in addition to :g:`term%scope` for opening a
  scope applying to all subterms)
  (`#14928 <https://github.com/coq/coq/pull/14928>`_,
  fixes `#11486 <https://github.com/coq/coq/issues/11486>`_
  and `#12157 <https://github.com/coq/coq/issues/12157>`_
  and `#14305 <https://github.com/coq/coq/issues/14305>`_,
  by Hugo Herbelin, reviewed by Pierre Roux).
- **Removed**
  the ability to declare scopes whose name starts with `_`
  (would be ambiguous with the new :g:`%_scope` notation)
  (`#14928 <https://github.com/coq/coq/pull/14928>`_,
  by Pierre Roux, reviewed by Hugo Herbelin).
- **Deprecated**
  the notation :n:`term%scope` in :cmd:`Arguments` command.
  In a few version, we'll make it an error and in next version give it
  the same semantics as in terms (i.e., deep scope opening for all
  subterms rather than just temporary opening)
  (`#14928 <https://github.com/coq/coq/pull/14928>`_,
  fixes `#11486 <https://github.com/coq/coq/issues/11486>`_
  and `#12157 <https://github.com/coq/coq/issues/12157>`_
  and `#14305 <https://github.com/coq/coq/issues/14305>`_,
  by Hugo Herbelin, reviewed by Pierre Roux).
