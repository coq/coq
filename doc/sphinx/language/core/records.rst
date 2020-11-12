.. _record-types:

Record types
----------------

The :cmd:`Record` construction is a macro allowing the definition of
records as is done in many programming languages. Its syntax is
described in the grammar below. In fact, the :cmd:`Record` macro is more general
than the usual record types, since it allows also for “manifest”
expressions. In this sense, the :cmd:`Record` construction allows defining
“signatures”.

.. _record_grammar:

.. cmd:: {| Record | Structure } @record_definition {* with @record_definition }
   :name: Record; Structure

   .. insertprodn record_definition field_def

   .. prodn::
      record_definition ::= {? > } @ident_decl {* @binder } {? : @sort } {? := {? @ident } %{ {*; @record_field } {? ; } %} }
      record_field ::= {* #[ {*, @attribute } ] } @name {? @field_body } {? %| @natural } {? @decl_notations }
      field_body ::= {* @binder } @of_type
      | {* @binder } @of_type := @term
      | {* @binder } := @term
      term_record ::= %{%| {*; @field_def } {? ; } %|%}
      field_def ::= @qualid {* @binder } := @term

   Each :n:`@record_definition` defines a record named by :n:`@ident_decl`.
   The constructor name is given by :n:`@ident`.
   If the constructor name is not specified, then the default name :n:`Build_@ident` is used,
   where :n:`@ident` is the record name.

   If :token:`sort` is omitted, the default sort is Type.
   Notice that the type of an identifier can depend on a previously-given identifier. Thus the
   order of the fields is important. :n:`@binder` parameters may be applied to the record as a whole
   or to individual fields.

   .. todo
      "Record foo2:Prop := { a }." gives the error "Cannot infer this placeholder of type "Type",
      while "Record foo2:Prop := { a:Type }." gives the output "foo2 is defined.
      a cannot be defined because it is informative and foo2 is not."
      Your thoughts?

   :n:`{? > }`
     If provided, the constructor name is automatically declared as
     a coercion from the class of the last field type to the record name
     (this may fail if the uniform inheritance condition is not
     satisfied).  See :ref:`coercions`.

   Notations can be attached to fields using the :n:`@decl_notations` annotation.

   :cmd:`Record` and :cmd:`Structure` are synonyms.

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(template)`, :attr:`universes(cumulative)`, and
   :attr:`private(matching)` attributes.

More generally, a record may have explicitly defined (a.k.a. manifest)
fields. For instance, we might have:
:n:`Record @ident {* @binder } : @sort := { @ident__1 : @type__1 ; @ident__2 := @term__2 ; @ident__3 : @type__3 }`.
in which case the correctness of :n:`@type__3` may rely on the instance :n:`@term__2` of :n:`@ident__2` and :n:`@term__2` may in turn depend on :n:`@ident__1`.

.. example::

   The set of rational numbers may be defined as:

   .. coqtop:: reset all

      Record Rat : Set := mkRat
       { sign : bool
       ; top : nat
       ; bottom : nat
       ; Rat_bottom_cond : 0 <> bottom
       ; Rat_irred_cond :
           forall x y z:nat, (x * y) = top /\ (x * z) = bottom -> x = 1
       }.

   Note here that the fields ``Rat_bottom_cond`` depends on the field ``bottom``
   and ``Rat_irred_cond`` depends on both ``top`` and ``bottom``.

Let us now see the work done by the ``Record`` macro. First the macro
generates a variant type definition with just one constructor:
:n:`Variant @ident {* @binder } : @sort := @ident__0 {* @binder }`.

To build an object of type :token:`ident`, provide the constructor
:n:`@ident__0` with the appropriate number of terms filling the fields of the record.

.. example::

   Let us define the rational :math:`1/2`:

    .. coqtop:: in

       Theorem one_two_irred : forall x y z:nat, x * y = 1 /\ x * z = 2 -> x = 1.
       Admitted.

       Definition half := mkRat true 1 2 (O_S 1) one_two_irred.
       Check half.

Alternatively, the following syntax allows creating objects by using named fields, as
shown in this grammar. The fields do not have to be in any particular order, nor do they have
to be all present if the missing ones can be inferred or prompted for
(see :ref:`programs`).

.. coqtop:: all

  Definition half' :=
    {| sign := true;
       Rat_bottom_cond := O_S 1;
       Rat_irred_cond := one_two_irred |}.

The following settings let you control the display format for types:

.. flag:: Printing Records

   If set, use the record syntax (shown above) as the default display format.

You can override the display format for specified types by adding entries to these tables:

.. table:: Printing Record @qualid
   :name: Printing Record

   Specifies a set of qualids which are displayed as records.  Use the
   :cmd:`Add` and :cmd:`Remove` commands to update the set of qualids.

.. table:: Printing Constructor @qualid
   :name: Printing Constructor

   Specifies a set of qualids which are displayed as constructors.  Use the
   :cmd:`Add` and :cmd:`Remove` commands to update the set of qualids.

This syntax can also be used for pattern matching.

.. coqtop:: all

   Eval compute in (
     match half with
     | {| sign := true; top := n |} => n
     | _ => 0
     end).

The macro generates also, when it is possible, the projection
functions for destructuring an object of type :token:`ident`. These
projection functions are given the names of the corresponding
fields. If a field is named `_` then no projection is built
for it. In our example:

.. coqtop:: all

  Eval compute in top half.
  Eval compute in bottom half.
  Eval compute in Rat_bottom_cond half.

An alternative syntax for projections based on a dot notation is
available:

.. coqtop:: all

   Eval compute in half.(top).

.. flag:: Printing Projections

   This flag activates the dot notation for printing.

   .. example::

      .. coqtop:: all

         Set Printing Projections.
         Check top half.

.. FIXME: move this to the main grammar in the spec chapter

.. _record_projections_grammar:

  .. insertprodn term_projection term_projection

  .. prodn::
     term_projection ::= @term0 .( @qualid {* @arg } )
     | @term0 .( @ @qualid {* @term1 } )

  Syntax of Record projections

The corresponding grammar rules are given in the preceding grammar. When :token:`qualid`
denotes a projection, the syntax :n:`@term0.(@qualid)` is equivalent to :n:`@qualid @term0`,
the syntax :n:`@term0.(@qualid {+ @arg })` to :n:`@qualid {+ @arg } @term0`.
and the syntax :n:`@term0.(@@qualid {+ @term0 })` to :n:`@@qualid {+ @term0 } @term0`.
In each case, :token:`term0` is the object projected and the
other arguments are the parameters of the inductive type.


.. note:: Records defined with the ``Record`` keyword are not allowed to be
   recursive (references to the record's name in the type of its field
   raises an  error). To define recursive records, one can use the ``Inductive``
   and ``CoInductive`` keywords, resulting in an inductive or co-inductive record.
   Definition of mutually inductive or co-inductive records are also allowed, as long
   as all of the types in the block are records.

.. note:: Induction schemes are automatically generated for inductive records.
   Automatic generation of induction schemes for non-recursive records
   defined with the ``Record`` keyword can be activated with the
   :flag:`Nonrecursive Elimination Schemes` flag (see :ref:`proofschemes-induction-principles`).

.. warn:: @ident cannot be defined.

  It can happen that the definition of a projection is impossible.
  This message is followed by an explanation of this impossibility.
  There may be three reasons:

  #. The name :token:`ident` already exists in the environment (see :cmd:`Axiom`).
  #. The body of :token:`ident` uses an incorrect elimination for
     :token:`ident` (see :cmd:`Fixpoint` and :ref:`Destructors`).
  #. The type of the projections :token:`ident` depends on previous
     projections which themselves could not be defined.

.. exn:: Records declared with the keyword Record or Structure cannot be recursive.

   The record name :token:`ident` appears in the type of its fields, but uses
   the keyword ``Record``. Use  the keyword ``Inductive`` or ``CoInductive`` instead.

.. exn:: Cannot handle mutually (co)inductive records.

   Records cannot be defined as part of mutually inductive (or
   co-inductive) definitions, whether with records only or mixed with
   standard definitions.

During the definition of the one-constructor inductive definition, all
the errors of inductive definitions, as described in Section
:ref:`gallina-inductive-definitions`, may also occur.

.. seealso:: Coercions and records in section :ref:`coercions-classes-as-records` of the chapter devoted to coercions.

.. _primitive_projections:

Primitive Projections
~~~~~~~~~~~~~~~~~~~~~

.. flag:: Primitive Projections

   Turns on the use of primitive
   projections when defining subsequent records (even through the ``Inductive``
   and ``CoInductive`` commands). Primitive projections
   extended the Calculus of Inductive Constructions with a new binary
   term constructor `r.(p)` representing a primitive projection `p` applied
   to a record object `r` (i.e., primitive projections are always applied).
   Even if the record type has parameters, these do not appear
   in the internal representation of
   applications of the projection, considerably reducing the sizes of
   terms when manipulating parameterized records and type checking time.
   On the user level, primitive projections can be used as a replacement
   for the usual defined ones, although there are a few notable differences.

.. flag:: Printing Primitive Projection Parameters

   This compatibility flag reconstructs internally omitted parameters at
   printing time (even though they are absent in the actual AST manipulated
   by the kernel).

Primitive Record Types
++++++++++++++++++++++

When the :flag:`Primitive Projections` flag is on, definitions of
record types change meaning. When a type is declared with primitive
projections, its :g:`match` construct is disabled (see :ref:`primitive_projections` though).
To eliminate the (co-)inductive type, one must use its defined primitive projections.

.. The following paragraph is quite redundant with what is above

For compatibility, the parameters still appear to the user when
printing terms even though they are absent in the actual AST
manipulated by the kernel. This can be changed by unsetting the
:flag:`Printing Primitive Projection Parameters` flag.

There are currently two ways to introduce primitive records types:

#. Through the ``Record`` command, in which case the type has to be
   non-recursive. The defined type enjoys eta-conversion definitionally,
   that is the generalized form of surjective pairing for records:
   `r` ``= Build_``\ `R` ``(``\ `r`\ ``.(``\ |p_1|\ ``) …`` `r`\ ``.(``\ |p_n|\ ``))``.
   Eta-conversion allows to define dependent elimination for these types as well.
#. Through the ``Inductive`` and ``CoInductive`` commands, when
   the body of the definition is a record declaration of the form
   ``Build_``\ `R` ``{`` |p_1| ``:`` |t_1|\ ``; … ;`` |p_n| ``:`` |t_n| ``}``.
   In this case the types can be recursive and eta-conversion is disallowed. These kind of record types
   differ from their traditional versions in the sense that dependent
   elimination is not available for them and only non-dependent case analysis
   can be defined.

Reduction
+++++++++

The basic reduction rule of a primitive projection is
|p_i| ``(Build_``\ `R` |t_1| … |t_n|\ ``)`` :math:`{\rightarrow_{\iota}}` |t_i|.
However, to take the :math:`{\delta}` flag into
account, projections can be in two states: folded or unfolded. An
unfolded primitive projection application obeys the rule above, while
the folded version delta-reduces to the unfolded version. This allows to
precisely mimic the usual unfolding rules of constants. Projections
obey the usual ``simpl`` flags of the ``Arguments`` command in particular.
There is currently no way to input unfolded primitive projections at the
user-level, and there is no way to display unfolded projections differently
from folded ones.


Compatibility Projections and :g:`match`
++++++++++++++++++++++++++++++++++++++++

To ease compatibility with ordinary record types, each primitive
projection is also defined as a ordinary constant taking parameters and
an object of the record type as arguments, and whose body is an
application of the unfolded primitive projection of the same name. These
constants are used when elaborating partial applications of the
projection. One can distinguish them from applications of the primitive
projection if the :flag:`Printing Primitive Projection Parameters` flag
is off: For a primitive projection application, parameters are printed
as underscores while for the compatibility projections they are printed
as usual.

Additionally, user-written :g:`match` constructs on primitive records
are desugared into substitution of the projections, they cannot be
printed back as :g:`match` constructs.
