- **Changed:**
  moved `print-mod-uid` from `rocq repl` to just `rocq`, removing risk of interaction with other `rocq repl` flags.
  `print-mod-uid` is an internal command used by `rocq makefile` when installing native compile data
  (`#22359 <https://github.com/rocq-prover/rocq/pull/22359>`_,
  by Gaëtan Gilbert).
