Definitions and theorems
========================

Definitions associate a specified term with a given name. The name can later
be replaced with its definition through :term:`δ-reduction`.  Definitions can
be local (defined with :g:`let`) or global
(e.g. defined with :cmd:`Definition` and related forms such as :cmd:`Fixpoint`
and :cmd:`CoFixpoint`).

On its side, a theorem is a statement with a proof. One can view
the name of a theorem as a way to abbreviate the given proof, in the
same way as the name of a definition abbreviates a term. That is, in
the case of definitions (and related forms such as :cmd:`Fixpoint` or
:cmd:`CoFixpoint`), the term is the body of the definition and the
type is the type of the body. In the case of a theorem, lemma,
corollary, etc. the term is the proof and the type is the statement.

Moreover, definitions can be local (defined with :g:`let`) or global
(defined at top-level).

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
   single: ... <: ... (VM type cast)
   single: ... <<: ... (native compute type cast)
   single: ... :> ... (volatile type cast)

.. _type-cast:

Type cast
---------

.. insertprodn term_cast term_cast

.. prodn::
   term_cast ::= @term10 : @type
   | @term10 <: @type
   | @term10 <<: @type
   | @term10 :> @type

The expression :n:`@term10 : @type` is a type cast expression. It enforces
the type of :n:`@term10` to be :n:`@type`.

:n:`@term10 <: @type` specifies that the virtual machine will be used
to type check that :n:`@term10` has type :n:`@type` (see :tacn:`vm_compute`).

:n:`@term10 <<: @type` specifies that compilation to OCaml will be used
to type check that :n:`@term10` has type :n:`@type` (see :tacn:`native_compute`).

:n:`@term10 :> @type` enforces the type of :n:`@term10` to be
:n:`@type` without leaving a trace in the produced value.
This is a :gdef:`volatile cast`.

If a scope is :ref:`bound <LocalInterpretationRulesForNotations>` to
:n:`@type` then :n:`@term10` is interpreted in that scope.

.. _gallina-definitions:

Top-level definitions
---------------------

Top-level definitions extend the global environment by associating names with terms.

The operation of unfolding a name into its definition is called
:term:`delta-reduction`.
A definition is accepted by the system if and only if the defined term is
well-typed in the current context of the definition and if the name is
not already used. The name defined by the definition is called a
:gdef:`constant` and the term it refers to is its :gdef:`body`. A definition has
a type, which is the type of its :term:`body`.

A formal presentation of constants and environments is given in
Section :ref:`typing-rules`.

.. cmd:: {| Definition | Example } @ident_decl @def_body
   :name: Definition; Example

   .. insertprodn def_body reduce

   .. prodn::
      def_body ::= {* @binder } {? : @type } := {? @reduce } @term
      | {* @binder } : @type
      reduce ::= Eval @red_expr in

   This binds :n:`@term` to the name :n:`@ident` in the global environment,
   provided that :n:`@term` is well-typed.

   If :n:`@type` is specified, the command checks that the type of :n:`@term`
   is definitionally equal to :n:`@type`.

   If :n:`@binder` is specified, it distributes over :n:`@term` and :n:`@type` as if they had
   respectively been :n:`fun {* @binder } => @term` and :n:`forall {* @binder }, @type`.

   If :n:`@reduce` is present then :n:`@ident` is bound to the result of the specified
   computation on :n:`@term`.

   If :n:`@term` is omitted, :n:`@type` is required and Rocq enters proof mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should normally be terminated with :cmd:`Defined`. See :ref:`proof-editing-mode`.

   The attributes :attr:`local`, :attr:`universes(polymorphic)`,
   :attr:`program` (see :ref:`program_definition`), :attr:`canonical`,
   :attr:`bypass_check(universes)`, :attr:`bypass_check(guard)`, :attr:`deprecated`,
   :attr:`warn` and :attr:`using` as well as the exclusive attributes :attr:`sealed`,
   :attr:`opaque` and :attr:`transparent`.

   .. seealso:: :cmd:`Opaque`, :cmd:`Transparent`, :tacn:`unfold`.

   .. exn:: @ident already exists.
      :name: ‘ident’ already exists. (Definition)
      :undocumented:

   .. exn:: The term @term has type @type while it is expected to have type @type'.
      :undocumented:

.. _Assertions:

Theorems and proofs
-------------------

Assertions, such as :cmd:`Theorem`s, state a proposition (or a type) for which the proof (or an
inhabitant of the type) is interactively built using :term:`tactics <tactic>`.
Assertions cause Rocq to enter :term:`proof mode` (see :ref:`proofhandling`).
Common tactics are described in the :ref:`writing-proofs` chapter.
The basic assertion command is:

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

   After the statement is asserted, Rocq needs a proof. Once a proof of
   :n:`@type` is given,
   the theorem is bound to the name :n:`@ident` in the global environment.

   If :n:`@binder` is specified, this behaves as if :n:`@type` had been
   :n:`forall {* @binder }, @type` and the proof starts in the context :n:`{* @binder }`.

   Forms using the :n:`with` clause are useful for theorems that are proved by simultaneous induction
   over a mutually inductive assumption, or that assert mutually dependent coinductive
   statements. It is equivalent to
   :cmd:`Fixpoint` or :cmd:`CoFixpoint` but using tactics to build the proof of
   the statements (or the :term:`body` of the specification, depending on the point of
   view). The inductive or coinductive types on which the induction or
   coinduction has to be done is guessed by the system.

   Like in a :cmd:`Fixpoint` or :cmd:`CoFixpoint` definition, the induction hypotheses
   have to be used on *structurally smaller* arguments (for a :cmd:`Fixpoint`) or
   be *guarded by a constructor* (for a :cmd:`CoFixpoint`). The verification that
   recursive proof arguments are correct is done only at the time of registering
   the lemma in the global environment. To know if the use of induction hypotheses is
   correct at some time of the interactive development of a proof, use the
   command :cmd:`Guarded`.

   The attributes :attr:`local`, :attr:`universes(polymorphic)`,
   :attr:`program` (see :ref:`program_lemma`),
   :attr:`bypass_check(universes)`, :attr:`bypass_check(guard)`, :attr:`deprecated`,
   :attr:`warn` and :attr:`using` are accepted.

   .. exn:: The term @term has type @type which should be Set, Prop or Type.
      :undocumented:

   .. exn:: @ident already exists.
      :name: ‘ident’ already exists. (Theorem)

      The name you provided is already defined. You have then to choose
      another name.

   .. exn:: Nested proofs are discouraged and not allowed by default. This error probably means that you forgot to close the last "Proof." with "Qed." or "Defined.". \
            If you really intended to use nested proofs, you can do so by turning the "Nested Proofs Allowed" flag on.

      You are asserting a new statement when you're already in proof mode.
      This feature, called nested proofs, is disabled by default.
      To activate it, turn the :flag:`Nested Proofs Allowed` flag on.

Proofs start with the keyword :cmd:`Proof`. Then Rocq enters the proof mode
until the proof is completed. In proof mode, the user primarily enters
tactics (see :ref:`writing-proofs`). The user may also enter
commands to manage the proof mode (see :ref:`proofhandling`).

When the proof is complete, use the :cmd:`Qed` command so the kernel verifies
the proof and adds it to the global environment. By default, proofs
that end with :cmd:`Qed` are sealed, that is that their content cannot
be unfolded (see :ref:`applyingconversionrules`), thus realizing
*proof irrelevance*, that is that only provability matters,
and not the exact proof. Proofs can be made unfoldable, as
definitions are, by using the :attr:`transparent` attribute or by ending
the proof with :cmd:`Defined` in place of :cmd:`Qed`. We
recommend using the attribute.

.. note::

   #. Several statements can be simultaneously asserted provided the
      :flag:`Nested Proofs Allowed` flag was turned on.

   #. Not only other assertions but any command can be given
      while in the process of proving a given assertion. In this case, the
      command is understood as if it would have been given before the
      statements still to be proved. Nonetheless, this practice is discouraged
      and may stop working in future versions.

   #. :cmd:`Proof` is recommended but can currently be omitted. On the opposite
      side, :cmd:`Qed` (or :cmd:`Defined`) is mandatory to validate a proof.

   #. One can also use :cmd:`Admitted` in place of :cmd:`Qed` to turn the
      current asserted statement into an axiom and exit proof mode.

Sealing, transparency and opacity
---------------------------------

Definitions and theorems can be sealed, transparent or opaque. Sealed
means that the body of the definition or the proof of the theorem are
abstract and cannot be unfolded. Transparent means that it can be
freely unfolded. Opaque means that it is unfoldable for type-checking
but kept abstract for reduction (see
e.g. :tacn:`unfold`). Transparency and opacity can be changed at any
time using the commands :cmd:`Transparent` and :cmd:`Opaque`. On the
other side, a sealed constant cannot be changed later to transparent
or opaque, nor a transparent or opaque constant be changed to sealed.

By default, definitions not built by tactics are
transparent. Definitions built interactively and ended with
:n:`Defined` are transparent. Theorems built interactively and ended
with :n:`Qed` are sealed. In the other cases, one of the following
attribute is expected:

.. attr:: sealed

.. attr:: transparent

.. attr:: opaque

Note that these attributes can be added either before the declaration
(e.g. :n:`#[sealed] Definition @ident := @term`) or before the name of
the constant (e.g. :n:`Definition #[sealed] @ident := @term`). When
several constants are declared at once (using :n:`with`), the
attribute given before the declaration is used as the default for all
names not themselves prefixed by an attribute.
