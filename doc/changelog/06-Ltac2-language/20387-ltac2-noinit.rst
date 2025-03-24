- **Changed:**
  Ltac2 does not depend on the prelude (i.e.  it is compiled with `-noinit`).
  It still depends on `Corelib.Init.Ltac` due to the interoperation with Ltac1
  (`#20387 <https://github.com/rocq-prover/rocq/pull/20387>`_,
  by Gaëtan Gilbert).
