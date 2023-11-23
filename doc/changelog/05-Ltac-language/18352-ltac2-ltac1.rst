- **Changed:**
  OCaml code common to Ltac1 and Ltac2 has been moved to a separate `ltacX_common_plugin`.
  Direct uses of :cmd:`Declare ML Module` for Ltac1 and Ltac2 need to ensure the common plugin was loaded previously,
  even when using findlib (findlib loads the OCaml code but does not activate the grammar effects)
  (no change is needed when loading the plugins by :cmd:`Require` of stdlib files, or the implicit prelude for Ltac1)
  (`#18352 <https://github.com/coq/coq/pull/18352>`_,
  by Gaëtan Gilbert).
