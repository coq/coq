- **Changed:**
  :cmd:`Ltac2 Set` only takes effect with shallow imports, i.e.
  `Import Foo` will not run a mutation from (non exported) inner module `Foo.Bar`
  (`#20516 <https://github.com/rocq-prover/rocq/pull/20516>`_,
  by Gaëtan Gilbert).
