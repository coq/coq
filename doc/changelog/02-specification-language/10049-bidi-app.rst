- New annotation in `Arguments` for bidirectionality hints: it is now possible
  to tell type inference to use type information from the context once the `n`
  first arguments of an application are known. The syntax is:
  `Arguments foo x y & z`.
  `#10049 <https://github.com/coq/coq/pull/10049>`_, by Maxime Dénès with
  help from Enrico Tassi
