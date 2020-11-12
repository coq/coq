Definitions
===========

.. index:: let ... := ... (term)

.. _let-in:

Let-in definitions
------------------

.. insertprodn term_let term_let

.. prodn::
   term_let ::= let @name {? : @type } := @term in @term
   | let @name {+ @binder } {? : @type } := @term in @term
   | @destructuring_let

:n:`let @ident := @term__1 in @term__2` represents the local binding of
the variable :n:`@ident` to the value :n:`@term__1` in :n:`@term__2`.

:n:`let @ident {+ @binder} := @term__1 in @term__2` is an abbreviation
for :n:`let @ident := fun {+ @binder} => @term__1 in @term__2`.

.. seealso::

   Extensions of the `let ... in ...` syntax are described in
   :ref:`irrefutable-patterns`.

.. index::
   single: ... : ... (type cast)
   single: ... <: ...
   single: ... <<: ...

Type cast
---------

.. insertprodn term_cast term_cast

.. prodn::
   term_cast ::= @term10 <: @type
   | @term10 <<: @type
   | @term10 : @type
   | @term10 :>

The expression :n:`@term10 : @type` is a type cast expression. It enforces
the type of :n:`@term10` to be :n:`@type`.

:n:`@term10 <: @type` locally sets up the virtual machine for checking that
:n:`@term10` has type :n:`@type`.

:n:`@term10 <<: @type` uses native compilation for checking that :n:`@term10`
has type :n:`@type`.

.. _gallina-definitions:

Top-level definitions
---------------------

Definitions extend the environment with associations of names to terms.
A definition can be seen as a way to give a meaning to a name or as a
way to abbreviate a term. In any case, the name can later be replaced at
any time by its definition.

The operation of unfolding a name into its definition is called
:math:`\delta`-conversion (see Section :ref:`delta-reduction`). A
definition is accepted by the system if and only if the defined term is
well-typed in the current context of the definition and if the name is
not already used. The name defined by the definition is called a
*constant* and the term it refers to is its *body*. A definition has a
type which is the type of its body.

A formal presentation of constants and environments is given in
Section :ref:`typing-rules`.

.. cmd:: {| Definition | Example } @ident_decl @def_body
   :name: Definition; Example

   .. insertprodn def_body reduce

   .. prodn::
      def_body ::= {* @binder } {? : @type } := {? @reduce } @term
      | {* @binder } : @type
      reduce ::= Eval @red_expr in

   These commands bind :n:`@term` to the name :n:`@ident` in the environment,
   provided that :n:`@term` is well-typed.  They can take the :attr:`local` :term:`attribute`,
   which makes the defined :n:`@ident` accessible by :cmd:`Import` and its variants
   only through their fully qualified names.
   If :n:`@reduce` is present then :n:`@ident` is bound to the result of the specified
   computation on :n:`@term`.

   These commands also support the :attr:`universes(polymorphic)`,
   :attr:`program` (see :ref:`program_definition`),
   :attr:`canonical` and :attr:`using` attributes.

   If :n:`@term` is omitted, :n:`@type` is required and Coq enters proof editing mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a constant
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.

   The form :n:`Definition @ident : @type := @term` checks that the type of :n:`@term`
   is definitionally equal to :n:`@type`, and registers :n:`@ident` as being of type
   :n:`@type`, and bound to value :n:`@term`.

   The form :n:`Definition @ident {* @binder } : @type := @term` is equivalent to
   :n:`Definition @ident : forall {* @binder }, @type := fun {* @binder } => @term`.

   .. seealso:: :cmd:`Opaque`, :cmd:`Transparent`, :tacn:`unfold`.

   .. exn:: @ident already exists.
      :name: @ident already exists. (Definition)
      :undocumented:

   .. exn:: The term @term has type @type while it is expected to have type @type'.
      :undocumented:

.. _Assertions:

Assertions and proofs
---------------------

An assertion states a proposition (or a type) of which the proof (or an
inhabitant of the type) is interactively built using tactics. The interactive
proof mode is described in Chapter :ref:`proofhandling` and the tactics in
Chapter :ref:`Tactics`. The basic assertion command is:

.. cmd:: @thm_token @ident_decl {* @binder } : @type {* with @ident_decl {* @binder } : @type }
   :name: Theorem; Lemma; Fact; Remark; Corollary; Proposition; Property

   .. insertprodn thm_token thm_token

   .. prodn::
      thm_token ::= Theorem
      | Lemma
      | Fact
      | Remark
      | Corollary
      | Proposition
      | Property

   After the statement is asserted, Coq needs a proof. Once a proof of
   :n:`@type` under the assumptions represented by :n:`@binder`\s is given and
   validated, the proof is generalized into a proof of :n:`forall {* @binder }, @type` and
   the theorem is bound to the name :n:`@ident` in the environment.

   These commands accept the :attr:`program` attribute.  See :ref:`program_lemma`.

   Forms using the :n:`with` clause are useful for theorems that are proved by simultaneous induction
   over a mutually inductive assumption, or that assert mutually dependent
   statements in some mutual co-inductive type. It is equivalent to
   :cmd:`Fixpoint` or :cmd:`CoFixpoint` but using tactics to build the proof of
   the statements (or the body of the specification, depending on the point of
   view). The inductive or co-inductive types on which the induction or
   coinduction has to be done is assumed to be non ambiguous and is guessed by
   the system.

   Like in a :cmd:`Fixpoint` or :cmd:`CoFixpoint` definition, the induction hypotheses
   have to be used on *structurally smaller* arguments (for a :cmd:`Fixpoint`) or
   be *guarded by a constructor* (for a :cmd:`CoFixpoint`). The verification that
   recursive proof arguments are correct is done only at the time of registering
   the lemma in the environment. To know if the use of induction hypotheses is
   correct at some time of the interactive development of a proof, use the
   command :cmd:`Guarded`.

   This command accepts the :attr:`using` attribute.

   .. exn:: The term @term has type @type which should be Set, Prop or Type.
      :undocumented:

   .. exn:: @ident already exists.
      :name: @ident already exists. (Theorem)

      The name you provided is already defined. You have then to choose
      another name.

   .. exn:: Nested proofs are not allowed unless you turn the Nested Proofs Allowed flag on.

      You are asserting a new statement while already being in proof editing mode.
      This feature, called nested proofs, is disabled by default.
      To activate it, turn the :flag:`Nested Proofs Allowed` flag on.

Proofs start with the keyword :cmd:`Proof`. Then Coq enters the proof editing mode
until the proof is completed. In proof editing mode, the user primarily enters
tactics, which are described in chapter :ref:`Tactics`. The user may also enter
commands to manage the proof editing mode. They are described in Chapter
:ref:`proofhandling`.

When the proof is complete, use the :cmd:`Qed` command so the kernel verifies
the proof and adds it to the environment.

.. note::

   #. Several statements can be simultaneously asserted provided the
      :flag:`Nested Proofs Allowed` flag was turned on.

   #. Not only other assertions but any vernacular command can be given
      while in the process of proving a given assertion. In this case, the
      command is understood as if it would have been given before the
      statements still to be proved. Nonetheless, this practice is discouraged
      and may stop working in future versions.

   #. Proofs ended by :cmd:`Qed` are declared opaque. Their content cannot be
      unfolded (see :ref:`performingcomputations`), thus
      realizing some form of *proof-irrelevance*. To be able to unfold a
      proof, the proof should be ended by :cmd:`Defined`.

   #. :cmd:`Proof` is recommended but can currently be omitted. On the opposite
      side, :cmd:`Qed` (or :cmd:`Defined`) is mandatory to validate a proof.

   #. One can also use :cmd:`Admitted` in place of :cmd:`Qed` to turn the
      current asserted statement into an axiom and exit the proof editing mode.
