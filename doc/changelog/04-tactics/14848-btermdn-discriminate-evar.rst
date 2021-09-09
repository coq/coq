- **Changed:**
  Use discrimination nets for goals containing evars in all
  :tacn:`auto` tactics. It essentially makes the behavior of undiscriminated
  databases to be the one of discriminated databases where all constants are
  considered transparent. This may be incompatible with previous behavior in
  very rare cases (`#14848 <https://github.com/coq/coq/pull/14848>`_,
  by Pierre-Marie Pédrot).
