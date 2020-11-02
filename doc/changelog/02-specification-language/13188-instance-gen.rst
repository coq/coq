- **Removed:** The type given to :cmd:`Instance` is no longer automatically
  generalized over unbound and :ref:`generalizable <implicit-generalization>` variables.
  Use :n:`Instance : \`{@type}` instead of :n:`Instance : @type` to get the old behaviour, or
  enable the compatibility flag :flag:`Instance Generalized Output`.
  (`#13188 <https://github.com/coq/coq/pull/13188>`_, fixes `#6042
  <https://github.com/coq/coq/issues/6042>`_, by Gaëtan Gilbert).
