- **Changed:**
  The syntax :n:`Derive x SuchThat type As name` is deprecated and replaced by
  :n:`Derive x in type as name` which itself is generalized into
  :n:`Derive open_binders in type as name`, so that several names,
  and possibly types to these names, can be given
  (`#19295 <https://github.com/coq/coq/pull/19295>`_,
  by Hugo Herbelin).
