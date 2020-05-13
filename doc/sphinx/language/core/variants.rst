Private (matching) inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. attr:: private(matching)

   This attribute can be used to forbid the use of the :g:`match`
   construct on objects of this inductive type outside of the module
   where it is defined.  There is also a legacy syntax using the
   ``Private`` prefix (cf. :n:`@legacy_attr`).

   The main use case of private (matching) inductive types is to emulate
   quotient types / higher-order inductive types in projects such as
   the `HoTT library <https://github.com/HoTT/HoTT>`_.

.. example::

   .. coqtop:: all

      Module Foo.
      #[ private(matching) ] Inductive my_nat := my_O : my_nat | my_S : my_nat -> my_nat.
      Check (fun x : my_nat => match x with my_O => true | my_S _ => false end).
      End Foo.
      Import Foo.
      Fail Check (fun x : my_nat => match x with my_O => true | my_S _ => false end).
