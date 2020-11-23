- **Changed:**
  In notations (except in custom entries), the misleading :n:`@syntax_modifier`
  :n:`@ident ident` (which accepted either an identifier or
  a :g:`_`) is deprecated and should be replaced by :n:`@ident name`. If
  the intent was really to only parse identifiers, this will
  eventually become possible, but only as of Coq 8.15.
  In custom entries, the meaning of :n:`@ident ident` is silently changed
  from parsing identifiers or :g:`_` to parsing only identifiers
  without warning, but this presumably affects only rare, recent and
  relatively experimental code
  (`#11841 <https://github.com/coq/coq/pull/11841>`_,
  fixes `#9514 <https://github.com/coq/coq/pull/9514>`_,
  by Hugo Herbelin).
