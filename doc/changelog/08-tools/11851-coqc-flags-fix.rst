- **Changed:**
  The order in which the require/load flags `-l`, `-ri`, `-re`, `-rfrom`, etc.
  and the option set flags `-set`, `-unset` are processed have been reversed.
  In the new behavior, require/load flags are processed before option flags.
  (`#11851 <https://github.com/coq/coq/pull/11851>`_,
  by Lasse Blaauwbroek).
