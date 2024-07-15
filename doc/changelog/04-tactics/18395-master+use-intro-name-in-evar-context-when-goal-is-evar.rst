- **Changed:**
  Tactic :g:`intro z` on an existential variable goal forces the resolution
  of the existential variable into a goal :g:`forall z:?T, ?P`, which
  becomes :g:`?P` in context :g:`z:?T` after introduction. The
  existential variable :n:`?P` itself is now defined in a context
  where the variable of type `?T` is also named :g:`z`, as specified
  by :tacn:`intro` instead of :g:`x` as it was conventionally the case
  before
  (`#18395 <https://github.com/coq/coq/pull/18395>`_,
  by Hugo Herbelin).
