- **Changed:**
  The order in which the require flags `-ri`, `-re`, `-rfrom`, etc.
  and the option flags `-set`, `-unset` are given now matters.  In
  particular, it is now possible to interleave the loading of plugins
  and the setting of options by choosing the right order for these
  flags.  The load flags `-l` and `-lv` are still processed afterward
  for now (`#11851 <https://github.com/coq/coq/pull/11851>`_ and
  `#12097 <https://github.com/coq/coq/pull/12097>`_,
  by Lasse Blaauwbroek).
