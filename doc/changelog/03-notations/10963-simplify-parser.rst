- A simplification of parsing rules could cause a slight change of
  parsing precedences for the very rare users who defined notations
  with `constr` at level stritcly between 100 and 200 and use these
  notations on the right-hand side of a cast operator (`:`, `:>`,
  `:>>`) (`#10963 <https://github.com/coq/coq/pull/10963>`_, by Théo
  Zimmermann, simplification initially noticed by Jim Fehrle).
