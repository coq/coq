- **Added:**
  :cmd:`Require` :n:`(safe)` loads a library and its dependencies with only
  kernel-level content and fully-qualified names.
  This is intended suitable for handling untrusted libraries (but may have caveats, see doc).
  A later plain :cmd:`Require` of a safe-loaded library errors
  (`#22291 <https://github.com/rocq-prover/rocq/pull/22291>`_,
  by Gaëtan Gilbert).
