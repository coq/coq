- **Fixed:**
  Type :n:`int` in files :n:`Number.v`, :n:`Decimal.v` and
  :n:`Hexadecimal.v` have been renamed to :n:`signed_int` (together
  with a compatibility alias :n:`int`) so that they can be used in
  extraction without conflicting with OCaml's :n:`int` type
  (`#13460 <https://github.com/coq/coq/pull/13460>`_,
  fixes `#7017 <https://github.com/coq/coq/issues/7017>`_
  and `#13288 <https://github.com/coq/coq/issues/13288>`_,
  by Hugo Herbelin).
