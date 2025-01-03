- **Deprecated:** module :g:`ZArith_Base`, :g:`Ztac`, and :g:`Zeq_bool`.
  Use :g:`ZArith` (or :g:`BinInt`), :g:`Lia`, and :g:`Z.eqb` instead.
  Reducing use of the deprecated modules in stdlib **changed** the transitive
  dependencies of several stdlib files; you may now need to ``Require``
  :g:`ZArith`, :g:`Lia`, :g:`Sumbool`.
  The definition of :g:`Zeq_bool` was also **changed** to be an alias for
  :g:`Z.eqb`; this is expected to simplify simultaneous compatibility with 8.20
  and 9.0
  (`#19801 <https://github.com/coq/coq/pull/19801>`_,
  by Andres Erbsen).
