- `coqc` now provides the ability to generate compiled interfaces.
  Use `coqc -vos foo.v` to skip all opaque proofs during the
  compilation of `foo.v`, and output a file called `foo.vos`.
  This feature enables working on a Coq file without the need to
  first compile the proofs contained in its dependencies
  (`#8642 <https://github.com/coq/coq/pull/8642>`_ by Arthur Charguéraud, review by
  Maxime Dénès and Emilio Gallego).
