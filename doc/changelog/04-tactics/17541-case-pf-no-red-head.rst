- **Changed:**
  the :tacn:`case` tactic and its variants always generate a
  pattern-matching node, regardless of their argument. In
  particular, they are now guaranteed to generate as many goals
  as there are constructors in the inductive type. Previously,
  they used to reduce to the corresponding branch when the argument
  βι-normalized to a constructor, resulting in a single goal
  (`#17541 <https://github.com/coq/coq/pull/17541>`_,
  by Pierre-Marie Pédrot).
