- A simplification of parsing rules could cause a slight change of
  parsing precedences for the very rare users who defined notations
  with `constr` at level strictly between 100 and 200 and used these
  notations on the right-hand side of a cast operator (`:`, `:>`,
  `:>>`) (`#10963 <https://github.com/coq/coq/pull/10963>`_, by Théo
  Zimmermann, simplification initially noticed by Jim Fehrle).
