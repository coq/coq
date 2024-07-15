- **Changed:**
  :cmd:`Variables` and its aliases does not share the type of combined binders anymore.
  This makes for instance `Variables a b : T` strictly equivalent to `Variables (a: T) (b : T).`
  (when `a` is not bound in `T`).
  The difference matters when interpreting `T` generates fresh universes or existential variables:
  they will be distinct in the types of `a` and `b`.
  This was already the case for binders in terms (eg `fun (a b : T) => ...`), :cmd:`Context`,
  and when :flag:`Universe Polymorphism` is enabled
  (`#19277 <https://github.com/coq/coq/pull/19277>`_,
  by Gaëtan Gilbert).
