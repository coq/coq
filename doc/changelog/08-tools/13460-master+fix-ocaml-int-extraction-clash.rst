- **Fixed:**
  Coq name :n:`int` can be used in extraction without conflicting with
  OCaml's :n:`int` type; additionally, to avoid possible conflicts in
  :cmd:`Extract Constant` or :cmd:`Extract Inductive`, the alias
  `__ocaml_int` can be used to refer to OCaml's :n:`int`
  (`#13460 <https://github.com/coq/coq/pull/13460>`_,
  fixes `#7017 <https://github.com/coq/coq/issues/7017>`_
  and `#13288 <https://github.com/coq/coq/issues/13288>`_,
  by Hugo Herbelin).
