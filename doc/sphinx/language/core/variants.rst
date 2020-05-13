Variants
~~~~~~~~

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
