Variants and the `match` construct
==================================

Variants
--------

.. cmd:: Variant @variant_definition {* with @variant_definition }

   .. insertprodn variant_definition variant_definition

   .. prodn::
      variant_definition ::= @ident_decl {* @binder } {? %| {* @binder } } {? : @type } := {? %| } {+| @constructor } {? @decl_notations }

   The :cmd:`Variant` command is similar to the :cmd:`Inductive` command, except
   that it disallows recursive definition of types (for instance, lists cannot
   be defined using :cmd:`Variant`). No induction scheme is generated for
   this variant, unless the :flag:`Nonrecursive Elimination Schemes` flag is on.

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(monomorphic)`, :attr:`universes(template)`,
   :attr:`universes(notemplate)`, :attr:`universes(cumulative)`,
   :attr:`universes(noncumulative)` and :attr:`private(matching)`
   attributes.

   .. exn:: The @num th argument of @ident must be @ident in @type.
      :undocumented:

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
