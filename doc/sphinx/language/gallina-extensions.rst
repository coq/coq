.. _extensionsofgallina:

Extensions of |Gallina|
=======================

|Gallina| is the kernel language of |Coq|. We describe here extensions of
|Gallina|’s syntax.

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

   .. insertprodn record_definition field_body

   .. prodn::
      record_definition ::= {? > } @ident_decl {* @binder } {? : @type } {? @ident } %{ {*; @record_field } %} {? @decl_notations }
      record_field ::= {* #[ {*, @attr } ] } @name {? @field_body } {? %| @num } {? @decl_notations }
      field_body ::= {* @binder } @of_type
      | {* @binder } @of_type := @term
      | {* @binder } := @term

   Each :n:`@record_definition` defines a record named by :n:`@ident_decl`.
   The constructor name is given by :n:`@ident`.
   If the constructor name is not specified, then the default name :n:`Build_@ident` is used,
   where :n:`@ident` is the record name.

   If :n:`@type` is
   omitted, the default type is :math:`\Type`. The identifiers inside the brackets are the field names.
   The type of each field :n:`@ident` is :n:`forall {* @binder }, @type`.
   Notice that the type of an identifier can depend on a previously-given identifier. Thus the
   order of the fields is important. :n:`@binder` parameters may be applied to the record as a whole
   or to individual fields.

   Notations can be attached to fields using the :n:`@decl_notations` annotation.

   :cmd:`Record` and :cmd:`Structure` are synonyms.

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(monomorphic)`, :attr:`universes(template)`,
   :attr:`universes(notemplate)`, :attr:`universes(cumulative)`,
   :attr:`universes(noncumulative)` and :attr:`private(matching)`
   attributes.

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

To build an object of type :token:`ident`, one should provide the constructor
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
   :cmd:`Add @table` and :cmd:`Remove @table` commands to update the set of qualids.

.. table:: Printing Constructor @qualid
   :name: Printing Constructor

   Specifies a set of qualids which are displayed as constructors.  Use the
   :cmd:`Add @table` and :cmd:`Remove @table` commands to update the set of qualids.

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

Variants and extensions of :g:`match`
-------------------------------------

.. _mult-match:

Multiple and nested pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The basic version of :g:`match` allows pattern matching on simple
patterns. As an extension, multiple nested patterns or disjunction of
patterns are allowed, as in ML-like languages.

The extension just acts as a macro that is expanded during parsing
into a sequence of match on simple patterns. Especially, a
construction defined using the extended match is generally printed
under its expanded form (see :flag:`Printing Matching`).

.. seealso:: :ref:`extendedpatternmatching`.

.. _if-then-else:

Pattern-matching on boolean values: the if expression
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For inductive types with exactly two constructors and for pattern matching
expressions that do not depend on the arguments of the constructors, it is possible
to use a ``if … then … else`` notation. For instance, the definition

.. coqtop:: all

   Definition not (b:bool) :=
   match b with
   | true => false
   | false => true
   end.

can be alternatively written

.. coqtop:: reset all

   Definition not (b:bool) := if b then false else true.

More generally, for an inductive type with constructors |C_1| and |C_2|,
we have the following equivalence

::

  if term [dep_ret_type] then term₁ else term₂ ≡
  match term [dep_ret_type] with
  | C₁ _ … _ => term₁
  | C₂ _ … _ => term₂
  end

.. example::

  .. coqtop:: all

     Check (fun x (H:{x=0}+{x<>0}) =>
     match H with
     | left _ => true
     | right _ => false
     end).

Notice that the printing uses the :g:`if` syntax because :g:`sumbool` is
declared as such (see :ref:`controlling-match-pp`).

.. _irrefutable-patterns:

Irrefutable patterns: the destructuring let variants
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Pattern-matching on terms inhabiting inductive type having only one
constructor can be alternatively written using :g:`let … in …`
constructions. There are two variants of them.


First destructuring let syntax
++++++++++++++++++++++++++++++

The expression :g:`let (`\ |ident_1|:g:`, … ,` |ident_n|\ :g:`) :=` |term_0|\ :g:`in` |term_1| performs
case analysis on |term_0| which must be in an inductive type with one
constructor having itself :math:`n` arguments. Variables |ident_1| … |ident_n| are
bound to the :math:`n` arguments of the constructor in expression |term_1|. For
instance, the definition

.. coqtop:: reset all

   Definition fst (A B:Set) (H:A * B) := match H with
   | pair x y => x
   end.

can be alternatively written

.. coqtop:: reset all

   Definition fst (A B:Set) (p:A * B) := let (x, _) := p in x.

Notice that reduction is different from regular :g:`let … in …`
construction since it happens only if |term_0| is in constructor form.
Otherwise, the reduction is blocked.

The pretty-printing of a definition by matching on a irrefutable
pattern can either be done using :g:`match` or the :g:`let` construction
(see Section :ref:`controlling-match-pp`).

If term inhabits an inductive type with one constructor `C`, we have an
equivalence between

::

   let (ident₁, …, identₙ) [dep_ret_type] := term in term'

and

::

   match term [dep_ret_type] with
   C ident₁ … identₙ => term'
   end


Second destructuring let syntax
+++++++++++++++++++++++++++++++

Another destructuring let syntax is available for inductive types with
one constructor by giving an arbitrary pattern instead of just a tuple
for all the arguments. For example, the preceding example can be
written:

.. coqtop:: reset all

   Definition fst (A B:Set) (p:A*B) := let 'pair x _ := p in x.

This is useful to match deeper inside tuples and also to use notations
for the pattern, as the syntax :g:`let ’p := t in b` allows arbitrary
patterns to do the deconstruction. For example:

.. coqtop:: all

   Definition deep_tuple (A:Set) (x:(A*A)*(A*A)) : A*A*A*A :=
   let '((a,b), (c, d)) := x in (a,b,c,d).

   Notation " x 'With' p " := (exist _ x p) (at level 20).

   Definition proj1_sig' (A:Set) (P:A->Prop) (t:{ x:A | P x }) : A :=
   let 'x With p := t in x.

When printing definitions which are written using this construct it
takes precedence over let printing directives for the datatype under
consideration (see Section :ref:`controlling-match-pp`).


.. _controlling-match-pp:

Controlling pretty-printing of match expressions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following commands give some control over the pretty-printing
of :g:`match` expressions.

Printing nested patterns
+++++++++++++++++++++++++

.. flag:: Printing Matching

   The Calculus of Inductive Constructions knows pattern matching only
   over simple patterns. It is however convenient to re-factorize nested
   pattern matching into a single pattern matching over a nested
   pattern.

   When this flag is on (default), |Coq|’s printer tries to do such
   limited re-factorization.
   Turning it off tells |Coq| to print only simple pattern matching problems
   in the same way as the |Coq| kernel handles them.


Factorization of clauses with same right-hand side
++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Printing Factorizable Match Patterns

   When several patterns share the same right-hand side, it is additionally
   possible to share the clauses using disjunctive patterns. Assuming that the
   printing matching mode is on, this flag (on by default) tells |Coq|'s
   printer to try to do this kind of factorization.

Use of a default clause
+++++++++++++++++++++++

.. flag:: Printing Allow Match Default Clause

   When several patterns share the same right-hand side which do not depend on the
   arguments of the patterns, yet an extra factorization is possible: the
   disjunction of patterns can be replaced with a `_` default clause. Assuming that
   the printing matching mode and the factorization mode are on, this flag (on by
   default) tells |Coq|'s printer to use a default clause when relevant.

Printing of wildcard patterns
++++++++++++++++++++++++++++++

.. flag:: Printing Wildcard

   Some variables in a pattern may not occur in the right-hand side of
   the pattern matching clause. When this flag is on (default), the
   variables having no occurrences in the right-hand side of the
   pattern matching clause are just printed using the wildcard symbol
   “_”.


Printing of the elimination predicate
+++++++++++++++++++++++++++++++++++++

.. flag:: Printing Synth

   In most of the cases, the type of the result of a matched term is
   mechanically synthesizable. Especially, if the result type does not
   depend of the matched term. When this flag is on (default),
   the result type is not printed when |Coq| knows that it can re-
   synthesize it.


Printing matching on irrefutable patterns
++++++++++++++++++++++++++++++++++++++++++

If an inductive type has just one constructor, pattern matching can be
written using the first destructuring let syntax.

.. table:: Printing Let @qualid
   :name: Printing Let

   Specifies a set of qualids for which pattern matching is displayed using a let expression.
   Note that this only applies to pattern matching instances entered with :g:`match`.
   It doesn't affect pattern matching explicitly entered with a destructuring
   :g:`let`.
   Use the :cmd:`Add @table` and :cmd:`Remove @table` commands to update this set.


Printing matching on booleans
+++++++++++++++++++++++++++++

If an inductive type is isomorphic to the boolean type, pattern matching
can be written using ``if`` … ``then`` … ``else`` ….  This table controls
which types are written this way:

.. table:: Printing If @qualid
   :name: Printing If

   Specifies a set of qualids for which pattern matching is displayed using
   ``if`` … ``then`` … ``else`` ….  Use the :cmd:`Add @table` and :cmd:`Remove @table`
   commands to update this set.

This example emphasizes what the printing settings offer.

.. example::

     .. coqtop:: all

       Definition snd (A B:Set) (H:A * B) := match H with
       | pair x y => y
       end.

       Test Printing Let for prod.

       Print snd.

       Remove Printing Let prod.

       Unset Printing Synth.

       Unset Printing Wildcard.

       Print snd.

.. _advanced-recursive-functions:
       
Advanced recursive functions
----------------------------

The following command is available when the ``FunInd`` library has been loaded via ``Require Import FunInd``:

.. cmd:: Function @fix_definition {* with @fix_definition }

   This command is a generalization of :cmd:`Fixpoint`. It is a wrapper
   for several ways of defining a function *and* other useful related
   objects, namely: an induction principle that reflects the recursive
   structure of the function (see :tacn:`function induction`) and its fixpoint equality.
   This defines a function similar to those defined by :cmd:`Fixpoint`.
   As in :cmd:`Fixpoint`, the decreasing argument must
   be given (unless the function is not recursive), but it might not
   necessarily be *structurally* decreasing. Use the :n:`@fixannot` clause
   to name the decreasing argument *and* to describe which kind of
   decreasing criteria to use to ensure termination of recursive
   calls.

   :cmd:`Function` also supports the :n:`with` clause to create
   mutually recursive definitions, however this feature is limited
   to structurally recursive functions (i.e. when :n:`@fixannot` is a :n:`struct`
   clause).

   See :tacn:`function induction` and :cmd:`Functional Scheme` for how to use
   the induction principle to reason easily about the function.

   The form of the :n:`@fixannot` clause determines which definition mechanism :cmd:`Function` uses.
   (Note that references to :n:`ident` below refer to the name of the function being defined.):

   *  If :n:`@fixannot` is not specified, :cmd:`Function`
      defines the nonrecursive function :token:`ident` as if it was declared with
      :cmd:`Definition`. In addition, the following are defined:

       + :token:`ident`\ ``_rect``, :token:`ident`\ ``_rec`` and :token:`ident`\ ``_ind``,
         which reflect the pattern matching structure of :token:`term` (see :cmd:`Inductive`);
       + The inductive :n:`R_@ident` corresponding to the graph of :token:`ident` (silently);
       + :token:`ident`\ ``_complete`` and :token:`ident`\ ``_correct`` which
         are inversion information linking the function and its graph.

   *  If :n:`{ struct ... }` is specified, :cmd:`Function`
      defines the structural recursive function :token:`ident` as if it was declared
      with :cmd:`Fixpoint`. In addition, the following are defined:

       + The same objects as above;
       + The fixpoint equation of :token:`ident`: :n:`@ident`\ ``_equation``.

   *  If :n:`{ measure ... }` or :n:`{ wf ... }` are specified, :cmd:`Function`
      defines a recursive function by well-founded recursion. The module ``Recdef``
      of the standard library must be loaded for this feature.

       + :n:`{measure @one_term__1 {? @ident } {? @one_term__2 } }`\: where :n:`@ident` is the decreasing argument
         and :n:`@one_term__1` is a function from the type of :n:`@ident` to :g:`nat` for which
         the decreasing argument decreases (for the :g:`lt` order on :g:`nat`)
         for each recursive call of the function. The parameters of the function are
         bound in :n:`@one_term__1`.
       + :n:`{wf @one_term @ident }`\: where :n:`@ident` is the decreasing argument and
         :n:`@one_term` is an ordering relation on the type of :n:`@ident` (i.e. of type
         `T`\ :math:`_{\sf ident}` → `T`\ :math:`_{\sf ident}` → ``Prop``) for which the decreasing argument
         decreases for each recursive call of the function. The order must be well-founded.
         The parameters of the function are bound in :n:`@one_term`.

      If the clause is ``measure`` or ``wf``, the user is left with some proof
      obligations that will be used to define the function. These proofs
      are: proofs that each recursive call is actually decreasing with
      respect to the given criteria, and (if the criteria is `wf`) a proof
      that the ordering relation is well-founded. Once proof obligations are
      discharged, the following objects are defined:

        + The same objects as with the ``struct`` clause;
        + The lemma :n:`@ident`\ ``_tcc`` which collects all proof obligations in one
          property;
        + The lemmas :n:`@ident`\ ``_terminate`` and :n:`@ident`\ ``_F`` which will be inlined
          during extraction of :n:`@ident`.

      The way this recursive function is defined is the subject of several
      papers by Yves Bertot and Antonia Balaa on the one hand, and Gilles
      Barthe, Julien Forest, David Pichardie, and Vlad Rusu on the other
      hand.

.. note::

   To obtain the right principle, it is better to put rigid
   parameters of the function as first arguments. For example it is
   better to define plus like this:

   .. coqtop:: reset none

      Require Import FunInd.

   .. coqtop:: all

      Function plus (m n : nat) {struct n} : nat :=
      match n with
      | 0 => m
      | S p => S (plus m p)
      end.

   than like this:

   .. coqtop:: reset none

      Require Import FunInd.

   .. coqtop:: all

      Function plus (n m : nat) {struct n} : nat :=
      match n with
      | 0 => m
      | S p => S (plus p m)
      end.


*Limitations*

:token:`term` must be built as a *pure pattern matching tree* (:g:`match … with`)
with applications only *at the end* of each branch.

:cmd:`Function` does not support partial application of the function being
defined. Thus, the following example cannot be accepted due to the
presence of partial application of :g:`wrong` in the body of :g:`wrong`:

.. coqtop:: none

   Require List.
   Import List.ListNotations.

.. coqtop:: all fail

   Function wrong (C:nat) : nat :=
     List.hd 0 (List.map wrong (C::nil)).

For now, dependent cases are not treated for non structurally
terminating functions.

.. exn:: The recursive argument must be specified.
   :undocumented:

.. exn:: No argument name @ident.
   :undocumented:

.. exn:: Cannot use mutual definition with well-founded recursion or measure.
   :undocumented:

.. warn:: Cannot define graph for @ident.

   The generation of the graph relation (:n:`R_@ident`) used to compute the induction scheme of ident
   raised a typing error. Only :token:`ident` is defined; the induction scheme
   will not be generated. This error happens generally when:

   - the definition uses pattern matching on dependent types,
     which :cmd:`Function` cannot deal with yet.
   - the definition is not a *pattern matching tree* as explained above.

.. warn:: Cannot define principle(s) for @ident.

   The generation of the graph relation (:n:`R_@ident`) succeeded but the induction principle
   could not be built. Only :token:`ident` is defined. Please report.

.. warn:: Cannot build functional inversion principle.

   :tacn:`functional inversion` will not be available for the function.

.. seealso:: :ref:`functional-scheme` and :tacn:`function induction`

.. _section-mechanism:

Section mechanism
-----------------

Sections create local contexts which can be shared across multiple definitions.

.. example::

   Sections are opened by the :cmd:`Section` command, and closed by :cmd:`End`.

   .. coqtop:: all

      Section s1.

   Inside a section, local parameters can be introduced using :cmd:`Variable`,
   :cmd:`Hypothesis`, or :cmd:`Context` (there are also plural variants for
   the first two).

   .. coqtop:: all

      Variables x y : nat.

   The command :cmd:`Let` introduces section-wide :ref:`let-in`. These definitions
   won't persist when the section is closed, and all persistent definitions which
   depend on `y'` will be prefixed with `let y' := y in`.

   .. coqtop:: in

      Let y' := y.
      Definition x' := S x.
      Definition x'' := x' + y'.

   .. coqtop:: all

      Print x'.
      Print x''.

      End s1.

      Print x'.
      Print x''.

   Notice the difference between the value of :g:`x'` and :g:`x''` inside section
   :g:`s1` and outside.

.. cmd:: Section @ident

   This command is used to open a section named :token:`ident`.
   Section names do not need to be unique.


.. cmd:: End @ident

   This command closes the section or module named :token:`ident`.
   See :ref:`Terminating an interactive module or module type definition<terminating_module>`
   for a description of its use with modules.

   After closing the
   section, the local declarations (variables and local definitions, see :cmd:`Variable`) are
   *discharged*, meaning that they stop being visible and that all global
   objects defined in the section are generalized with respect to the
   variables and local definitions they each depended on in the section.

   .. exn:: There is nothing to end.
      :undocumented:

   .. exn:: Last block to end has name @ident.
       :undocumented:

.. note::
   Most commands, like :cmd:`Hint`, :cmd:`Notation`, option management, … which
   appear inside a section are canceled when the section is closed.

.. cmd:: Let @ident @def_body
         Let Fixpoint @fix_definition {* with @fix_definition }
         Let CoFixpoint @cofix_definition {* with @cofix_definition }
   :name: Let; Let Fixpoint; Let CoFixpoint

   These commands behave like :cmd:`Definition`, :cmd:`Fixpoint` and :cmd:`CoFixpoint`, except that
   the declared constant is local to the current section.
   When the section is closed, all persistent
   definitions and theorems within it that depend on the constant
   will be wrapped with a :n:`@term_let` with the same declaration.

   As for :cmd:`Definition`, :cmd:`Fixpoint` and :cmd:`CoFixpoint`,
   if :n:`@term` is omitted, :n:`@type` is required and Coq enters proof editing mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a constant
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.

.. cmd:: Context {+ @binder }

   Declare variables in the context of the current section, like :cmd:`Variable`,
   but also allowing implicit variables, :ref:`implicit-generalization`, and
   let-binders.

   .. coqdoc::

     Context {A : Type} (a b : A).
     Context `{EqDec A}.
     Context (b' := b).

.. seealso:: Section :ref:`binders`. Section :ref:`contexts` in chapter :ref:`typeclasses`.

Module system
-------------

The module system provides a way of packaging related elements
together, as well as a means of massive abstraction.


.. cmd:: Module {? {| Import | Export } } @ident {* @module_binder } {? @of_module_type } {? := {+<+ @module_expr_inl } }

   .. insertprodn module_binder module_expr_inl

   .. prodn::
      module_binder ::= ( {? {| Import | Export } } {+ @ident } : @module_type_inl )
      module_type_inl ::= ! @module_type
      | @module_type {? @functor_app_annot }
      functor_app_annot ::= [ inline at level @num ]
      | [ no inline ]
      module_type ::= @qualid
      | ( @module_type )
      | @module_type @module_expr_atom
      | @module_type with @with_declaration
      with_declaration ::= Definition @qualid {? @univ_decl } := @term
      | Module @qualid := @qualid
      module_expr_atom ::= @qualid
      | ( {+ @module_expr_atom } )
      of_module_type ::= : @module_type_inl
      | {* <: @module_type_inl }
      module_expr_inl ::= ! {+ @module_expr_atom }
      | {+ @module_expr_atom } {? @functor_app_annot }

   Defines a module named :token:`ident`.  See the examples :ref:`here<module_examples>`.

   The :n:`Import` and :n:`Export` flags specify whether the module should be automatically
   imported or exported.

   Specifying :n:`{* @module_binder }` starts a functor with
   parameters given by the :n:`@module_binder`\s.  (A *functor* is a function
   from modules to modules.)

   .. todo: would like to find a better term than "interactive", not very descriptive

   :n:`@of_module_type` specifies the module type.  :n:`{+ <: @module_type_inl }`
   starts a module that satisfies each :n:`@module_type_inl`.

   :n:`:= {+<+ @module_expr_inl }` specifies the body of a module or functor
   definition.  If it's not specified, then the module is defined *interactively*,
   meaning that the module is defined as a series of commands terminated with :cmd:`End`
   instead of in a single :cmd:`Module` command.
   Interactively defining the :n:`@module_expr_inl`\s in a series of
   :cmd:`Include` commands is equivalent to giving them all in a single
   non-interactive :cmd:`Module` command.

   The ! prefix indicates that any assumption command (such as :cmd:`Axiom`) with an :n:`Inline` clause
   in the type of the functor arguments will be ignored.

   .. todo: What is an Inline directive?  sb command but still unclear.  Maybe referring to the
      "inline" in functor_app_annot?  or assumption_token Inline assum_list?

.. cmd:: Module Type @ident {* @module_binder } {* <: @module_type_inl } {? := {+<+ @module_type_inl } }

   Defines a module type named :n:`@ident`.  See the example :ref:`here<example_def_simple_module_type>`.

   Specifying :n:`{* @module_binder }` starts a functor type with
   parameters given by the :n:`@module_binder`\s.

   :n:`:= {+<+ @module_type_inl }` specifies the body of a module or functor type
   definition.  If it's not specified, then the module type is defined *interactively*,
   meaning that the module type is defined as a series of commands terminated with :cmd:`End`
   instead of in a single :cmd:`Module Type` command.
   Interactively defining the :n:`@module_type_inl`\s in a series of
   :cmd:`Include` commands is equivalent to giving them all in a single
   non-interactive :cmd:`Module Type` command.

.. _terminating_module:

**Terminating an interactive module or module type definition**

Interactive modules are terminated with the :cmd:`End` command, which
is also used to terminate :ref:`Sections<section-mechanism>`.
:n:`End @ident` closes the interactive module or module type :token:`ident`.
If the module type was given, the command verifies that the content of the module
matches the module type.  If the module is not a
functor, its components (constants, inductive types, submodules etc.)
are now available through the dot notation.

.. exn:: No such label @ident.
    :undocumented:

.. exn:: Signature components for label @ident do not match.
    :undocumented:

.. exn:: The field @ident is missing in @qualid.
   :undocumented:

.. |br| raw:: html

    <br>

.. note::

  #. Interactive modules and module types can be nested.
  #. Interactive modules and module types can't be defined inside of :ref:`sections<section-mechanism>`.
     Sections can be defined inside of interactive modules and module types.
  #. Hints and notations (:cmd:`Hint` and :cmd:`Notation` commands) can also appear inside interactive
     modules and module types. Note that with module definitions like:

     :n:`Module @ident__1 : @module_type := @ident__2.`

     or

     :n:`Module @ident__1 : @module_type.` |br|
     :n:`Include @ident__2.` |br|
     :n:`End @ident__1.`

     hints and the like valid for :n:`@ident__1` are the ones defined in :n:`@module_type`
     rather then those defined in :n:`@ident__2` (or the module body).
  #. Within an interactive module type definition, the :cmd:`Parameter` command declares a
     constant instead of definining a new axiom (which it does when not in a module type definition).
  #. Assumptions such as :cmd:`Axiom` that include the :n:`Inline` clause will be automatically
     expanded when the functor is applied, except when the function application is prefixed by ``!``.

.. cmd:: Include @module_type_inl {* <+ @module_expr_inl }

   Includes the content of module(s) in the current
   interactive module. Here :n:`@module_type_inl` can be a module expression or a module
   type expression. If it is a high-order module or module type
   expression then the system tries to instantiate :n:`@module_type_inl` with the current
   interactive module.

   Including multiple modules is a single :cmd:`Include` is equivalent to including each module
   in a separate :cmd:`Include` command.

.. cmd:: Include Type @module_type_inl {* <+ @module_type_inl }

   .. deprecated:: 8.3

      Use :cmd:`Include` instead.

.. cmd:: Declare Module {? {| Import | Export } } @ident {* @module_binder } : @module_type_inl

   Declares a module :token:`ident` of type :token:`module_type_inl`.

   If :n:`@module_binder`\s are specified, declares a functor with parameters given by the list of
   :token:`module_binder`\s.

.. cmd:: Import {+ @qualid }

   If :token:`qualid` denotes a valid basic module (i.e. its module type is a
   signature), makes its components available by their short names.

   .. example::

      .. coqtop:: reset in

         Module Mod.
         Definition T:=nat.
         Check T.
         End Mod.
         Check Mod.T.

      .. coqtop:: all

         Fail Check T.
         Import Mod.
         Check T.

   Some features defined in modules are activated only when a module is
   imported. This is for instance the case of notations (see :ref:`Notations`).

   Declarations made with the :attr:`local` attribute are never imported by the :cmd:`Import`
   command. Such declarations are only accessible through their fully
   qualified name.

   .. example::

      .. coqtop:: in

         Module A.
         Module B.
         Local Definition T := nat.
         End B.
         End A.
         Import A.

      .. coqtop:: all fail

         Check B.T.

.. cmd:: Export {+ @qualid }
   :name: Export

   Similar to :cmd:`Import`, except that when the module containing this command
   is imported, the :n:`{+ @qualid }` are imported as well.

   .. exn:: @qualid is not a module.
      :undocumented:

   .. warn:: Trying to mask the absolute name @qualid!
      :undocumented:

.. cmd:: Print Module @qualid

   Prints the module type and (optionally) the body of the module :n:`@qualid`.

.. cmd:: Print Module Type @qualid

   Prints the module type corresponding to :n:`@qualid`.

.. flag:: Short Module Printing

   This flag (off by default) disables the printing of the types of fields,
   leaving only their names, for the commands :cmd:`Print Module` and
   :cmd:`Print Module Type`.

.. _module_examples:

Examples
~~~~~~~~

.. example:: Defining a simple module interactively

    .. coqtop:: in

       Module M.
       Definition T := nat.
       Definition x := 0.

    .. coqtop:: all

       Definition y : bool.
       exact true.

    .. coqtop:: in

       Defined.
       End M.

Inside a module one can define constants, prove theorems and do anything
else that can be done in the toplevel. Components of a closed
module can be accessed using the dot notation:

.. coqtop:: all

   Print M.x.

.. _example_def_simple_module_type:

.. example:: Defining a simple module type interactively

   .. coqtop:: in

      Module Type SIG.
      Parameter T : Set.
      Parameter x : T.
      End SIG.

.. _example_filter_module:

.. example:: Creating a new module that omits some items from an existing module

   Since :n:`SIG`, the type of the new module :n:`N`, doesn't define :n:`y` or
   give the body of :n:`x`, which are not included in :n:`N`.

   .. coqtop:: all

      Module N : SIG with Definition T := nat := M.
      Print N.T.
      Print N.x.
      Fail Print N.y.

   .. reset to remove N (undo in last coqtop block doesn't seem to do that), invisibly redefine M, SIG
   .. coqtop:: none reset

      Module M.
      Definition T := nat.
      Definition x := 0.
      Definition y : bool.
      exact true.
      Defined.
      End M.

      Module Type SIG.
      Parameter T : Set.
      Parameter x : T.
      End SIG.

The following definition of :g:`N` using the module type expression :g:`SIG` with
:g:`Definition T := nat` is equivalent to the following one:

.. todo: what is other definition referred to above?
   "Module N' : SIG with Definition T := nat. End N`." is not it.

.. coqtop:: in

   Module Type SIG'.
   Definition T : Set := nat.
   Parameter x : T.
   End SIG'.

   Module N : SIG' := M.

If we just want to be sure that our implementation satisfies a
given module type without restricting the interface, we can use a
transparent constraint

.. coqtop:: in

   Module P <: SIG := M.

.. coqtop:: all

   Print P.y.

.. example:: Creating a functor (a module with parameters)

   .. coqtop:: in

      Module Two (X Y: SIG).
      Definition T := (X.T * Y.T)%type.
      Definition x := (X.x, Y.x).
      End Two.

   and apply it to our modules and do some computations:

   .. coqtop:: in


      Module Q := Two M N.

   .. coqtop:: all

      Eval compute in (fst Q.x + snd Q.x).

.. example:: A module type with two sub-modules, sharing some fields

   .. coqtop:: in

      Module Type SIG2.
        Declare Module M1 : SIG.
        Module M2 <: SIG.
          Definition T := M1.T.
          Parameter x : T.
        End M2.
      End SIG2.

   .. coqtop:: in

      Module Mod <: SIG2.
        Module M1.
          Definition T := nat.
          Definition x := 1.
        End M1.
      Module M2 := M.
      End Mod.

Notice that ``M`` is a correct body for the component ``M2`` since its ``T``
component is ``nat`` as specified for ``M1.T``.

Libraries and qualified names
---------------------------------

.. _names-of-libraries:

Names of libraries
~~~~~~~~~~~~~~~~~~

The theories developed in |Coq| are stored in *library files* which are
hierarchically classified into *libraries* and *sublibraries*. To
express this hierarchy, library names are represented by qualified
identifiers qualid, i.e. as list of identifiers separated by dots (see
:ref:`gallina-identifiers`). For instance, the library file ``Mult`` of the standard
|Coq| library ``Arith`` is named ``Coq.Arith.Mult``. The identifier that starts
the name of a library is called a *library root*. All library files of
the standard library of |Coq| have the reserved root |Coq| but library
filenames based on other roots can be obtained by using |Coq| commands
(coqc, coqtop, coqdep, …) options ``-Q`` or ``-R`` (see :ref:`command-line-options`).
Also, when an interactive |Coq| session starts, a library of root ``Top`` is
started, unless option ``-top`` or ``-notop`` is set (see :ref:`command-line-options`).

.. _qualified-names:

Qualified names
~~~~~~~~~~~~~~~

Library files are modules which possibly contain submodules which
eventually contain constructions (axioms, parameters, definitions,
lemmas, theorems, remarks or facts). The *absolute name*, or *full
name*, of a construction in some library file is a qualified
identifier starting with the logical name of the library file,
followed by the sequence of submodules names encapsulating the
construction and ended by the proper name of the construction.
Typically, the absolute name ``Coq.Init.Logic.eq`` denotes Leibniz’
equality defined in the module Logic in the sublibrary ``Init`` of the
standard library of |Coq|.

The proper name that ends the name of a construction is the short name
(or sometimes base name) of the construction (for instance, the short
name of ``Coq.Init.Logic.eq`` is ``eq``). Any partial suffix of the absolute
name is a *partially qualified name* (e.g. ``Logic.eq`` is a partially
qualified name for ``Coq.Init.Logic.eq``). Especially, the short name of a
construction is its shortest partially qualified name.

|Coq| does not accept two constructions (definition, theorem, …) with
the same absolute name but different constructions can have the same
short name (or even same partially qualified names as soon as the full
names are different).

Notice that the notion of absolute, partially qualified and short
names also applies to library filenames.

**Visibility**

|Coq| maintains a table called the name table which maps partially qualified
names of constructions to absolute names. This table is updated by the
commands :cmd:`Require`, :cmd:`Import` and :cmd:`Export` and
also each time a new declaration is added to the context. An absolute
name is called visible from a given short or partially qualified name
when this latter name is enough to denote it. This means that the
short or partially qualified name is mapped to the absolute name in
|Coq| name table. Definitions with the :attr:`local` attribute are only accessible with
their fully qualified name (see :ref:`gallina-definitions`).

It may happen that a visible name is hidden by the short name or a
qualified name of another construction. In this case, the name that
has been hidden must be referred to using one more level of
qualification. To ensure that a construction always remains
accessible, absolute names can never be hidden.

.. example::

    .. coqtop:: all

       Check 0.

       Definition nat := bool.

       Check 0.

       Check Datatypes.nat.

       Locate nat.

.. seealso:: Commands :cmd:`Locate` and :cmd:`Locate Library`.

.. _libraries-and-filesystem:

Libraries and filesystem
~~~~~~~~~~~~~~~~~~~~~~~~

.. note:: The questions described here have been subject to redesign in |Coq| 8.5.
   Former versions of |Coq| use the same terminology to describe slightly different things.

Compiled files (``.vo`` and ``.vio``) store sub-libraries. In order to refer
to them inside |Coq|, a translation from file-system names to |Coq| names
is needed. In this translation, names in the file system are called
*physical* paths while |Coq| names are contrastingly called *logical*
names.

A logical prefix Lib can be associated with a physical path using
the command line option ``-Q`` `path` ``Lib``. All subfolders of path are
recursively associated to the logical path ``Lib`` extended with the
corresponding suffix coming from the physical path. For instance, the
folder ``path/fOO/Bar`` maps to ``Lib.fOO.Bar``. Subdirectories corresponding
to invalid |Coq| identifiers are skipped, and, by convention,
subdirectories named ``CVS`` or ``_darcs`` are skipped too.

Thanks to this mechanism, ``.vo`` files are made available through the
logical name of the folder they are in, extended with their own
basename. For example, the name associated to the file
``path/fOO/Bar/File.vo`` is ``Lib.fOO.Bar.File``. The same caveat applies for
invalid identifiers. When compiling a source file, the ``.vo`` file stores
its logical name, so that an error is issued if it is loaded with the
wrong loadpath afterwards.

Some folders have a special status and are automatically put in the
path. |Coq| commands associate automatically a logical path to files in
the repository trees rooted at the directory from where the command is
launched, ``coqlib/user-contrib/``, the directories listed in the
``$COQPATH``, ``${XDG_DATA_HOME}/coq/`` and ``${XDG_DATA_DIRS}/coq/``
environment variables (see `XDG base directory specification
<http://standards.freedesktop.org/basedir-spec/basedir-spec-latest.html>`_)
with the same physical-to-logical translation and with an empty logical prefix.

The command line option ``-R`` is a variant of ``-Q`` which has the strictly
same behavior regarding loadpaths, but which also makes the
corresponding ``.vo`` files available through their short names in a way
similar to the :cmd:`Import` command. For instance, ``-R path Lib``
associates to the file ``/path/fOO/Bar/File.vo`` the logical name
``Lib.fOO.Bar.File``, but allows this file to be accessed through the
short names ``fOO.Bar.File,Bar.File`` and ``File``. If several files with
identical base name are present in different subdirectories of a
recursive loadpath, which of these files is found first may be system-
dependent and explicit qualification is recommended. The ``From`` argument
of the ``Require`` command can be used to bypass the implicit shortening
by providing an absolute root to the required file (see :ref:`compiled-files`).

There also exists another independent loadpath mechanism attached to
OCaml object files (``.cmo`` or ``.cmxs``) rather than |Coq| object
files as described above. The OCaml loadpath is managed using
the option ``-I`` `path` (in the OCaml world, there is neither a
notion of logical name prefix nor a way to access files in
subdirectories of path). See the command :cmd:`Declare ML Module` in
:ref:`compiled-files` to understand the need of the OCaml loadpath.

See :ref:`command-line-options` for a more general view over the |Coq| command
line options.

.. _ImplicitArguments:

Implicit arguments
------------------

An implicit argument of a function is an argument which can be
inferred from contextual knowledge. There are different kinds of
implicit arguments that can be considered implicit in different ways.
There are also various commands to control the setting or the
inference of implicit arguments.


The different kinds of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Implicit arguments inferable from the knowledge of other arguments of a function
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

The first kind of implicit arguments covers the arguments that are
inferable from the knowledge of the type of other arguments of the
function, or of the type of the surrounding context of the
application. Especially, such implicit arguments correspond to
parameters dependent in the type of the function. Typical implicit
arguments are the type arguments in polymorphic functions. There are
several kinds of such implicit arguments.

**Strict Implicit Arguments**

An implicit argument can be either strict or non strict. An implicit
argument is said to be *strict* if, whatever the other arguments of the
function are, it is still inferable from the type of some other
argument. Technically, an implicit argument is strict if it
corresponds to a parameter which is not applied to a variable which
itself is another parameter of the function (since this parameter may
erase its arguments), not in the body of a match, and not itself
applied or matched against patterns (since the original form of the
argument can be lost by reduction).

For instance, the first argument of
::

  cons: forall A:Set, A -> list A -> list A

in module ``List.v`` is strict because :g:`list` is an inductive type and :g:`A`
will always be inferable from the type :g:`list A` of the third argument of
:g:`cons`. Also, the first argument of :g:`cons` is strict with respect to the second one,
since the first argument is exactly the type of the second argument.
On the contrary, the second argument of a term of type
::

  forall P:nat->Prop, forall n:nat, P n -> ex nat P

is implicit but not strict, since it can only be inferred from the
type :g:`P n` of the third argument and if :g:`P` is, e.g., :g:`fun _ => True`, it
reduces to an expression where ``n`` does not occur any longer. The first
argument :g:`P` is implicit but not strict either because it can only be
inferred from :g:`P n` and :g:`P` is not canonically inferable from an arbitrary
:g:`n` and the normal form of :g:`P n`. Consider, e.g., that :g:`n` is :math:`0` and the third
argument has type :g:`True`, then any :g:`P` of the form
::

  fun n => match n with 0 => True | _ => anything end

would be a solution of the inference problem.

**Contextual Implicit Arguments**

An implicit argument can be *contextual* or not. An implicit argument
is said *contextual* if it can be inferred only from the knowledge of
the type of the context of the current expression. For instance, the
only argument of::

  nil : forall A:Set, list A`

is contextual. Similarly, both arguments of a term of type::

  forall P:nat->Prop, forall n:nat, P n \/ n = 0

are contextual (moreover, :g:`n` is strict and :g:`P` is not).

**Reversible-Pattern Implicit Arguments**

There is another class of implicit arguments that can be reinferred
unambiguously if all the types of the remaining arguments are known.
This is the class of implicit arguments occurring in the type of
another argument in position of reversible pattern, which means it is
at the head of an application but applied only to uninstantiated
distinct variables. Such an implicit argument is called *reversible-
pattern implicit argument*. A typical example is the argument :g:`P` of
nat_rec in
::

  nat_rec : forall P : nat -> Set, P 0 ->
    (forall n : nat, P n -> P (S n)) -> forall x : nat, P x

(:g:`P` is reinferable by abstracting over :g:`n` in the type :g:`P n`).

See :ref:`controlling-rev-pattern-implicit-args` for the automatic declaration of reversible-pattern
implicit arguments.

Implicit arguments inferable by resolution
++++++++++++++++++++++++++++++++++++++++++

This corresponds to a class of non-dependent implicit arguments that
are solved based on the structure of their type only.


Maximal or non maximal insertion of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In case a function is partially applied, and the next argument to be
applied is an implicit argument, two disciplines are applicable. In
the first case, the function is considered to have no arguments
furtherly: one says that the implicit argument is not maximally
inserted. In the second case, the function is considered to be
implicitly applied to the implicit arguments it is waiting for: one
says that the implicit argument is maximally inserted.

Each implicit argument can be declared to be inserted maximally or non
maximally. In Coq, maximally-inserted implicit arguments are written between curly braces
"{ }" and non-maximally-inserted implicit arguments are written in square brackets "[ ]".

.. seealso:: :flag:`Maximal Implicit Insertion`

Trailing Implicit Arguments
+++++++++++++++++++++++++++

An implicit argument is considered trailing when all following arguments are declared
implicit. Trailing implicit arguments cannot be declared non maximally inserted,
otherwise they would never be inserted.

.. exn:: Argument @name is a trailing implicit, so it can't be declared non maximal. Please use %{ %} instead of [ ].

   For instance:

   .. coqtop:: all fail

      Fail Definition double [n] := n + n.


Casual use of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In a given expression, if it is clear that some argument of a function
can be inferred from the type of the other arguments, the user can
force the given argument to be guessed by replacing it by “_”. If
possible, the correct argument will be automatically generated.

.. exn:: Cannot infer a term for this placeholder.
   :name: Cannot infer a term for this placeholder. (Casual use of implicit arguments)

   |Coq| was not able to deduce an instantiation of a “_”.

.. _declare-implicit-args:

Declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In case one wants that some arguments of a given object (constant,
inductive types, constructors, assumptions, local or not) are always
inferred by |Coq|, one may declare once and for all which are the
expected implicit arguments of this object. There are two ways to do
this, *a priori* and *a posteriori*.


Implicit Argument Binders
+++++++++++++++++++++++++

.. insertprodn implicit_binders implicit_binders

.. prodn::
   implicit_binders ::= %{ {+ @name } {? : @type } %}
   | [ {+ @name } {? : @type } ]

In the first setting, one wants to explicitly give the implicit
arguments of a declared object as part of its definition. To do this,
one has to surround the bindings of implicit arguments by curly
braces or square braces:

.. coqtop:: all

   Definition id {A : Type} (x : A) : A := x.

This automatically declares the argument A of id as a maximally
inserted implicit argument. One can then do as-if the argument was
absent in every situation but still be able to specify it if needed:

.. coqtop:: all

   Definition compose {A B C} (g : B -> C) (f : A -> B) := fun x => g (f x).

   Goal forall A, compose id id = id (A:=A).

For non maximally inserted implicit arguments, use square brackets:

.. coqtop:: all

   Fixpoint map [A B : Type] (f : A -> B) (l : list A) : list B :=
     match l with
     | nil => nil
     | cons a t => cons (f a) (map f t)
     end.

   Print Implicit map.

The syntax is supported in all top-level definitions:
:cmd:`Definition`, :cmd:`Fixpoint`, :cmd:`Lemma` and so on. For (co-)inductive datatype
declarations, the semantics are the following: an inductive parameter
declared as an implicit argument need not be repeated in the inductive
definition and will become implicit for the inductive type and the constructors.
For example:

.. coqtop:: all

   Inductive list {A : Type} : Type :=
   | nil : list
   | cons : A -> list -> list.

   Print list.

One can always specify the parameter if it is not uniform using the
usual implicit arguments disambiguation syntax.

The syntax is also supported in internal binders. For instance, in the
following kinds of expressions, the type of each declaration present
in :token:`binders` can be bracketed to mark the declaration as
implicit:
:n:`fun (@ident:forall {* @binder }, @type) => @term`,
:n:`forall (@ident:forall {* @binder }, @type), @type`,
:n:`let @ident {* @binder } := @term in @term`,
:n:`fix @ident {* @binder } := @term in @term` and
:n:`cofix @ident {* @binder } := @term in @term`.
Here is an example:

.. coqtop:: all

   Axiom Ax :
     forall (f:forall {A} (a:A), A * A),
     let g {A} (x y:A) := (x,y) in
     f 0 = g 0 0.

.. warn:: Ignoring implicit binder declaration in unexpected position

   This is triggered when setting an argument implicit in an
   expression which does not correspond to the type of an assumption
   or to the body of a definition. Here is an example:

   .. coqtop:: all warn

      Definition f := forall {y}, y = 0.

.. warn:: Making shadowed name of implicit argument accessible by position

   This is triggered when two variables of same name are set implicit
   in the same block of binders, in which case the first occurrence is
   considered to be unnamed. Here is an example:

   .. coqtop:: all warn

      Check let g {x:nat} (H:x=x) {x} (H:x=x) := x in 0.


Declaring Implicit Arguments
++++++++++++++++++++++++++++



.. cmd:: Arguments @smart_qualid {* @argument_spec_block } {* , {* @more_implicits_block } } {? : {+, @arguments_modifier } }
   :name: Arguments

   .. insertprodn smart_qualid arguments_modifier

   .. prodn::
      smart_qualid ::= @qualid
      | @by_notation
      by_notation ::= @string {? % @ident }
      argument_spec_block ::= @argument_spec
      | /
      | &
      | ( {+ @argument_spec } ) {? % @ident }
      | [ {+ @argument_spec } ] {? % @ident }
      | %{ {+ @argument_spec } %} {? % @ident }
      argument_spec ::= {? ! } @name {? % @ident }
      more_implicits_block ::= @name
      | [ {+ @name } ]
      | %{ {+ @name } %}
      arguments_modifier ::= simpl nomatch
      | simpl never
      | default implicits
      | clear bidirectionality hint
      | clear implicits
      | clear scopes
      | clear scopes and implicits
      | clear implicits and scopes
      | rename
      | assert
      | extra scopes

   This command sets implicit arguments *a posteriori*,
   where the list of :n:`@name`\s is a prefix of the list of
   arguments of :n:`@smart_qualid`.  Arguments in square
   brackets are declared as implicit and arguments in curly brackets are declared as
   maximally inserted.

   After the command is issued, implicit arguments can and must be
   omitted in any expression that applies :token:`qualid`.

   This command supports the :attr:`local` and :attr:`global` attributes.
   Default behavior is to limit the effect to the current section but also to
   extend their effect outside the current module or library file.
   Applying :attr:`local` limits the effect of the command to the current module if
   it's not in a section.  Applying :attr:`global` within a section extends the
   effect outside the current sections and current module if the command occurs.

   A command containing :n:`@argument_spec_block & @argument_spec_block`
   provides :ref:`bidirectionality_hints`.

   Use the :n:`@more_implicits_block` to specify multiple implicit arguments declarations
   for names of constants, inductive types, constructors and lemmas that can only be
   applied to a fixed number of arguments (excluding, for instance,
   constants whose type is polymorphic).
   The longest applicable list of implicit arguments will be used to select which
   implicit arguments are inserted.
   For printing, the omitted arguments are the ones of the longest list of implicit
   arguments of the sequence.  See the example :ref:`here<example_more_implicits>`.

   The :n:`@arguments_modifier` values have various effects:

   * :n:`clear implicits` - clears implicit arguments
   * :n:`default implicits` - automatically determine the implicit arguments of the object.
     See :ref:`auto_decl_implicit_args`.
   * :n:`rename` - rename implicit arguments for the object
   * :n:`assert` - assert that the object has the expected number of arguments with the
     expected names.  See the example here: :ref:`renaming_implicit_arguments`.

.. exn:: The / modifier may only occur once.
   :undocumented:

.. exn:: The & modifier may only occur once.
   :undocumented:

.. example::

    .. coqtop:: reset all

       Inductive list (A : Type) : Type :=
       | nil : list A
       | cons : A -> list A -> list A.

       Check (cons nat 3 (nil nat)).

       Arguments cons [A] _ _.

       Arguments nil {A}.

       Check (cons 3 nil).

       Fixpoint map (A B : Type) (f : A -> B) (l : list A) : list B :=
         match l with nil => nil | cons a t => cons (f a) (map A B f t) end.

       Fixpoint length (A : Type) (l : list A) : nat :=
         match l with nil => 0 | cons _ m => S (length A m) end.

       Arguments map [A B] f l.

       Arguments length {A} l. (* A has to be maximally inserted *)

       Check (fun l:list (list nat) => map length l).

.. _example_more_implicits:

.. example:: Multiple implicit arguments with :n:`@more_implicits_block`

   .. coqtop:: all

       Arguments map [A B] f l, [A] B f l, A B f l.

       Check (fun l => map length l = map (list nat) nat length l).

.. note::
   Use the :cmd:`Print Implicit` command to see the implicit arguments
   of an object (see :ref:`displaying-implicit-args`).

.. _auto_decl_implicit_args:

Automatic declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The :n:`default implicits @arguments_modifier` clause tells |Coq| to automatically determine the
   implicit arguments of the object.

   Auto-detection is governed by flags specifying whether strict,
   contextual, or reversible-pattern implicit arguments must be
   considered or not (see :ref:`controlling-strict-implicit-args`, :ref:`controlling-contextual-implicit-args`,
   :ref:`controlling-rev-pattern-implicit-args` and also :ref:`controlling-insertion-implicit-args`).

.. example:: Default implicits

   .. coqtop:: reset all

       Inductive list (A:Set) : Set :=
       | nil : list A
       | cons : A -> list A -> list A.

       Arguments cons : default implicits.

       Print Implicit cons.

       Arguments nil : default implicits.

       Print Implicit nil.

       Set Contextual Implicit.

       Arguments nil : default implicits.

       Print Implicit nil.

The computation of implicit arguments takes account of the unfolding
of constants. For instance, the variable ``p`` below has type
``(Transitivity R)`` which is reducible to
``forall x,y:U, R x y -> forall z:U, R y z -> R x z``. As the variables ``x``, ``y`` and ``z``
appear strictly in the body of the type, they are implicit.

.. coqtop:: all

   Parameter X : Type.

   Definition Relation := X -> X -> Prop.

   Definition Transitivity (R:Relation) := forall x y:X, R x y -> forall z:X, R y z -> R x z.

   Parameters (R : Relation) (p : Transitivity R).

   Arguments p : default implicits.

   Print p.

   Print Implicit p.

   Parameters (a b c : X) (r1 : R a b) (r2 : R b c).

   Check (p r1 r2).


Mode for automatic declaration of implicit arguments
++++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Implicit Arguments

   This flag (off by default) allows to systematically declare implicit
   the arguments detectable as such. Auto-detection of implicit arguments is
   governed by flags controlling whether strict and contextual implicit
   arguments have to be considered or not.

.. _controlling-strict-implicit-args:

Controlling strict implicit arguments
+++++++++++++++++++++++++++++++++++++

.. flag:: Strict Implicit

   When the mode for automatic declaration of implicit arguments is on,
   the default is to automatically set implicit only the strict implicit
   arguments plus, for historical reasons, a small subset of the non-strict
   implicit arguments. To relax this constraint and to set
   implicit all non strict implicit arguments by default, you can turn this
   flag off.

.. flag:: Strongly Strict Implicit

   Use this flag (off by default) to capture exactly the strict implicit
   arguments and no more than the strict implicit arguments.

.. _controlling-contextual-implicit-args:

Controlling contextual implicit arguments
+++++++++++++++++++++++++++++++++++++++++

.. flag:: Contextual Implicit

   By default, |Coq| does not automatically set implicit the contextual
   implicit arguments. You can turn this flag on to tell |Coq| to also
   infer contextual implicit argument.

.. _controlling-rev-pattern-implicit-args:

Controlling reversible-pattern implicit arguments
+++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Reversible Pattern Implicit

   By default, |Coq| does not automatically set implicit the reversible-pattern
   implicit arguments. You can turn this flag on to tell |Coq| to also infer
   reversible-pattern implicit argument.

.. _controlling-insertion-implicit-args:

Controlling the insertion of implicit arguments not followed by explicit arguments
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Maximal Implicit Insertion

   Assuming the implicit argument mode is on, this flag (off by default)
   declares implicit arguments to be automatically inserted when a
   function is partially applied and the next argument of the function is
   an implicit one.

Combining manual declaration and automatic declaration
++++++++++++++++++++++++++++++++++++++++++++++++++++++

When some arguments are manually specified implicit with binders in a definition
and the automatic declaration mode in on, the manual implicit arguments are added to the
automatically declared ones.

In that case, and when the flag :flag:`Maximal Implicit Insertion` is set to off,
some trailing implicit arguments can be inferred to be non maximally inserted. In
this case, they are converted to maximally inserted ones.

.. example::

   .. coqtop:: all

      Set Implicit Arguments.
      Axiom eq0_le0 : forall (n : nat) (x : n = 0), n <= 0.
      Print Implicit eq0_le0.
      Axiom eq0_le0' : forall (n : nat) {x : n = 0}, n <= 0.
      Print Implicit eq0_le0'.


.. _explicit-applications:

Explicit applications
~~~~~~~~~~~~~~~~~~~~~

In presence of non-strict or contextual arguments, or in presence of
partial applications, the synthesis of implicit arguments may fail, so
one may have to explicitly give certain implicit arguments of an
application. Use the :n:`(@ident := @term)` form of :token:`arg` to do so,
where :token:`ident` is the name of the implicit argument and :token:`term`
is its corresponding explicit term. Alternatively, one can deactivate
the hiding of implicit arguments for a single function application using the
:n:`@ @qualid {? @univ_annot } {* @term1 }` form of :token:`term10`.

.. example:: Syntax for explicitly giving implicit arguments (continued)

    .. coqtop:: all

       Check (p r1 (z:=c)).

       Check (p (x:=a) (y:=b) r1 (z:=c) r2).


.. _renaming_implicit_arguments:

Renaming implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. example:: (continued)  Renaming implicit arguments

   .. coqtop:: all

      Arguments p [s t] _ [u] _: rename.

      Check (p r1 (u:=c)).

      Check (p (s:=a) (t:=b) r1 (u:=c) r2).

      Fail Arguments p [s t] _ [w] _ : assert.

.. _displaying-implicit-args:

Displaying implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Implicit @smart_qualid

   Displays the implicit arguments associated with an object,
   identifying which arguments are applied maximally or not.


Displaying implicit arguments when pretty-printing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Implicit

   By default, the basic pretty-printing rules hide the inferrable implicit
   arguments of an application. Turn this flag on to force printing all
   implicit arguments.

.. flag:: Printing Implicit Defensive

   By default, the basic pretty-printing rules display implicit
   arguments that are not detected as strict implicit arguments. This
   “defensive” mode can quickly make the display cumbersome so this can
   be deactivated by turning this flag off.

.. seealso:: :flag:`Printing All`.

Interaction with subtyping
~~~~~~~~~~~~~~~~~~~~~~~~~~

When an implicit argument can be inferred from the type of more than
one of the other arguments, then only the type of the first of these
arguments is taken into account, and not an upper type of all of them.
As a consequence, the inference of the implicit argument of “=” fails
in

.. coqtop:: all

   Fail Check nat = Prop.

but succeeds in

.. coqtop:: all

   Check Prop = nat.


Deactivation of implicit arguments for parsing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Parsing Explicit

   Turning this flag on (it is off by default) deactivates the use of implicit arguments.

   In this case, all arguments of constants, inductive types,
   constructors, etc, including the arguments declared as implicit, have
   to be given as if no arguments were implicit. By symmetry, this also
   affects printing.

.. _canonical-structure-declaration:

Canonical structures
~~~~~~~~~~~~~~~~~~~~

A canonical structure is an instance of a record/structure type that
can be used to solve unification problems involving a projection
applied to an unknown structure instance (an implicit argument) and a
value. The complete documentation of canonical structures can be found
in :ref:`canonicalstructures`; here only a simple example is given.

.. cmd:: Canonical {? Structure } @smart_qualid
         Canonical {? Structure } @ident_decl @def_body
   :name: Canonical Structure; _

   The first form of this command declares an existing :n:`@smart_qualid` as a
   canonical instance of a structure (a record).

   The second form defines a new constant as if the :cmd:`Definition` command
   had been used, then declares it as a canonical instance as if the first
   form had been used on the defined object.

   This command supports the :attr:`local` attribute.  When used, the
   structure is canonical only within the :cmd:`Section` containing it.

   Assume that :token:`qualid` denotes an object ``(Build_struct`` |c_1| … |c_n| ``)`` in the
   structure :g:`struct` of which the fields are |x_1|, …, |x_n|.
   Then, each time an equation of the form ``(``\ |x_i| ``_)`` |eq_beta_delta_iota_zeta| |c_i| has to be
   solved during the type checking process, :token:`qualid` is used as a solution.
   Otherwise said, :token:`qualid` is canonically used to extend the field |c_i|
   into a complete structure built on |c_i|.

   Canonical structures are particularly useful when mixed with coercions
   and strict implicit arguments.

   .. example::

      Here is an example.

      .. coqtop:: all

         Require Import Relations.

         Require Import EqNat.

         Set Implicit Arguments.

         Unset Strict Implicit.

         Structure Setoid : Type := {Carrier :> Set; Equal : relation Carrier;
                                     Prf_equiv : equivalence Carrier Equal}.

         Definition is_law (A B:Setoid) (f:A -> B) := forall x y:A, Equal x y -> Equal (f x) (f y).

         Axiom eq_nat_equiv : equivalence nat eq_nat.

         Definition nat_setoid : Setoid := Build_Setoid eq_nat_equiv.

         Canonical nat_setoid.

      Thanks to :g:`nat_setoid` declared as canonical, the implicit arguments :g:`A`
      and :g:`B` can be synthesized in the next statement.

      .. coqtop:: all abort

         Lemma is_law_S : is_law S.

   .. note::
      If a same field occurs in several canonical structures, then
      only the structure declared first as canonical is considered.

   .. attr:: canonical(false)

      To prevent a field from being involved in the inference of
      canonical instances, its declaration can be annotated with the
      :attr:`canonical(false)` attribute (cf. the syntax of
      :n:`@record_field`).

      .. example::

         For instance, when declaring the :g:`Setoid` structure above, the
         :g:`Prf_equiv` field declaration could be written as follows.

         .. coqdoc::

            #[canonical(false)] Prf_equiv : equivalence Carrier Equal

      See :ref:`canonicalstructures` for a more realistic example.

.. attr:: canonical

   This attribute can decorate a :cmd:`Definition` or :cmd:`Let` command.
   It is equivalent to having a :cmd:`Canonical Structure` declaration just
   after the command.

.. cmd:: Print Canonical Projections {* @smart_qualid }

   This displays the list of global names that are components of some
   canonical structure. For each of them, the canonical structure of
   which it is a projection is indicated. If constants are given as
   its arguments, only the unification rules that involve or are
   synthesized from simultaneously all given constants will be shown.

   .. example::

      For instance, the above example gives the following output:

      .. coqtop:: all

         Print Canonical Projections.

      .. coqtop:: all

         Print Canonical Projections nat.

      .. note::

         The last line in the first example would not show up if the
         corresponding projection (namely :g:`Prf_equiv`) were annotated as not
         canonical, as described above.

Implicit types of variables
~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is possible to bind variable names to a given type (e.g. in a
development using arithmetic, it may be convenient to bind the names :g:`n`
or :g:`m` to the type :g:`nat` of natural numbers).

.. cmd:: Implicit {| Type | Types } @reserv_list
   :name: Implicit Type; Implicit Types

   .. insertprodn reserv_list simple_reserv

   .. prodn::
      reserv_list ::= {+ ( @simple_reserv ) }
      | @simple_reserv
      simple_reserv ::= {+ @ident } : @type

   Sets the type of bound
   variables starting with :token:`ident` (either :token:`ident` itself or
   :token:`ident` followed by one or more single quotes, underscore or
   digits) to :token:`type` (unless the bound variable is already declared
   with an explicit type, in which case, that type will be used).

.. example::

    .. coqtop:: all

       Require Import List.

       Implicit Types m n : nat.

       Lemma cons_inj_nat : forall m n l, n :: l = m :: l -> n = m.
       Proof. intros m n. Abort.

       Lemma cons_inj_bool : forall (m n:bool) l, n :: l = m :: l -> n = m.
       Abort.

.. flag:: Printing Use Implicit Types

  By default, the type of bound variables is not printed when
  the variable name is associated to an implicit type which matches the
  actual type of the variable. This feature can be deactivated by
  turning this flag off.

.. _implicit-generalization:

Implicit generalization
~~~~~~~~~~~~~~~~~~~~~~~

.. index:: `{ }
.. index:: `[ ]
.. index:: `( )
.. index:: `{! }
.. index:: `[! ]
.. index:: `(! )

.. insertprodn generalizing_binder typeclass_constraint

.. prodn::
   generalizing_binder ::= `( {+, @typeclass_constraint } )
   | `%{ {+, @typeclass_constraint } %}
   | `[ {+, @typeclass_constraint } ]
   typeclass_constraint ::= {? ! } @term
   | %{ @name %} : {? ! } @term
   | @name : {? ! } @term


Implicit generalization is an automatic elaboration of a statement
with free variables into a closed statement where these variables are
quantified explicitly.  Use the :cmd:`Generalizable` command to designate
which variables should be generalized.

It is activated for a binder by prefixing a \`, and for terms by
surrounding it with \`{ }, or \`[ ] or \`( ).

Terms surrounded by \`{ } introduce their free variables as maximally
inserted implicit arguments, terms surrounded by \`[ ] introduce them as
non maximally inserted implicit arguments and terms surrounded by \`( )
introduce them as explicit arguments.

Generalizing binders always introduce their free variables as
maximally inserted implicit arguments. The binder itself introduces
its argument as usual.

In the following statement, ``A`` and ``y`` are automatically
generalized, ``A`` is implicit and ``x``, ``y`` and the anonymous
equality argument are explicit.

.. coqtop:: all reset

   Generalizable All Variables.

   Definition sym `(x:A) : `(x = y -> y = x) := fun _ p => eq_sym p.

   Print sym.

Dually to normal binders, the name is optional but the type is required:

.. coqtop:: all

   Check (forall `{x = y :> A}, y = x).

When generalizing a binder whose type is a typeclass, its own class
arguments are omitted from the syntax and are generalized using
automatic names, without instance search. Other arguments are also
generalized unless provided. This produces a fully general statement.
this behaviour may be disabled by prefixing the type with a ``!`` or
by forcing the typeclass name to be an explicit application using
``@`` (however the later ignores implicit argument information).

.. coqtop:: all

   Class Op (A:Type) := op : A -> A -> A.

   Class Commutative (A:Type) `(Op A) := commutative : forall x y, op x y = op y x.
   Instance nat_op : Op nat := plus.

   Set Printing Implicit.
   Check (forall `{Commutative }, True).
   Check (forall `{Commutative nat}, True).
   Fail Check (forall `{Commutative nat _}, True).
   Fail Check (forall `{!Commutative nat}, True).
   Arguments Commutative _ {_}.
   Check (forall `{!Commutative nat}, True).
   Check (forall `{@Commutative nat plus}, True).

Multiple binders can be merged using ``,`` as a separator:

.. coqtop:: all

   Check (forall `{Commutative A, Hnat : !Commutative nat}, True).

.. cmd:: Generalizable {| {| Variable | Variables } {+ @ident } | All Variables | No Variables }

   Controls the set of generalizable identifiers.  By default, no variables are
   generalizable.

   This command supports the :attr:`global` attribute.

   The :n:`{| Variable | Variables } {+ @ident }` form allows generalization of only the given :n:`@ident`\s.
   Using this command multiple times adds to the allowed identifiers.  The other forms clear
   the list of :n:`@ident`\s.

   The :n:`All Variables` form generalizes all free variables in
   the context that appear under a
   generalization delimiter. This may result in confusing errors in case
   of typos. In such cases, the context will probably contain some
   unexpected generalized variables.

   The :n:`No Variables` form disables implicit generalization entirely.  This is
   the default behavior (before any :cmd:`Generalizable` command has been entered).


.. _Coercions:

Coercions
---------

Coercions can be used to implicitly inject terms from one *class* in
which they reside into another one. A *class* is either a sort
(denoted by the keyword ``Sortclass``), a product type (denoted by the
keyword ``Funclass``), or a type constructor (denoted by its name), e.g.
an inductive type or any constant with a type of the form
``forall (`` |x_1| : |A_1| ) … ``(``\ |x_n| : |A_n|\ ``)``, `s` where `s` is a sort.

Then the user is able to apply an object that is not a function, but
can be coerced to a function, and more generally to consider that a
term of type ``A`` is of type ``B`` provided that there is a declared coercion
between ``A`` and ``B``.

More details and examples, and a description of the commands related
to coercions are provided in :ref:`implicitcoercions`.

.. _printing_constructions_full:

Printing constructions in full
------------------------------

.. flag:: Printing All

   Coercions, implicit arguments, the type of pattern matching, but also
   notations (see :ref:`syntaxextensionsandinterpretationscopes`) can obfuscate the behavior of some
   tactics (typically the tactics applying to occurrences of subterms are
   sensitive to the implicit arguments). Turning this flag on
   deactivates all high-level printing features such as coercions,
   implicit arguments, returned type of pattern matching, notations and
   various syntactic sugar for pattern matching or record projections.
   Otherwise said, :flag:`Printing All` includes the effects of the flags
   :flag:`Printing Implicit`, :flag:`Printing Coercions`, :flag:`Printing Synth`,
   :flag:`Printing Projections`, and :flag:`Printing Notations`. To reactivate
   the high-level printing features, use the command ``Unset Printing All``.

.. _printing-universes:

Printing universes
------------------

.. flag:: Printing Universes

   Turn this flag on to activate the display of the actual level of each
   occurrence of :g:`Type`. See :ref:`Sorts` for details. This wizard flag, in
   combination with :flag:`Printing All` can help to diagnose failures to unify
   terms apparently identical but internally different in the Calculus of Inductive
   Constructions.

.. cmd:: Print {? Sorted } Universes {? Subgraph ( {* @qualid } ) } {? @string }
   :name: Print Universes

   This command can be used to print the constraints on the internal level
   of the occurrences of :math:`\Type` (see :ref:`Sorts`).

   The :n:`Subgraph` clause limits the printed graph to the requested names (adjusting
   constraints to preserve the implied transitive constraints between
   kept universes).

   The :n:`Sorted` clause makes each universe
   equivalent to a numbered label reflecting its level (with a linear
   ordering) in the universe hierarchy.

   :n:`@string` is an optional output filename.
   If :n:`@string` ends in ``.dot`` or ``.gv``, the constraints are printed in the DOT
   language, and can be processed by Graphviz tools. The format is
   unspecified if `string` doesn’t end in ``.dot`` or ``.gv``.

.. _existential-variables:

Existential variables
---------------------

.. insertprodn term_evar term_evar

.. prodn::
   term_evar ::= ?[ @ident ]
   | ?[ ?@ident ]
   | ?@ident {? @%{ {+; @ident := @term } %} }

|Coq| terms can include existential variables which represents unknown
subterms to eventually be replaced by actual subterms.

Existential variables are generated in place of unsolvable implicit
arguments or “_” placeholders when using commands such as ``Check`` (see
Section :ref:`requests-to-the-environment`) or when using tactics such as
:tacn:`refine`, as well as in place of unsolvable instances when using
tactics such that :tacn:`eapply`. An existential
variable is defined in a context, which is the context of variables of
the placeholder which generated the existential variable, and a type,
which is the expected type of the placeholder.

As a consequence of typing constraints, existential variables can be
duplicated in such a way that they possibly appear in different
contexts than their defining context. Thus, any occurrence of a given
existential variable comes with an instance of its original context.
In the simple case, when an existential variable denotes the
placeholder which generated it, or is used in the same context as the
one in which it was generated, the context is not displayed and the
existential variable is represented by “?” followed by an identifier.

.. coqtop:: all

   Parameter identity : forall (X:Set), X -> X.

   Check identity _ _.

   Check identity _ (fun x => _).

In the general case, when an existential variable :n:`?@ident` appears
outside of its context of definition, its instance, written under the
form :n:`{ {*; @ident := @term} }` is appending to its name, indicating
how the variables of its defining context are instantiated.
The variables of the context of the existential variables which are
instantiated by themselves are not written, unless the :flag:`Printing Existential Instances` flag
is on (see Section :ref:`explicit-display-existentials`), and this is why an
existential variable used in the same context as its context of definition is written with no instance.

.. coqtop:: all

   Check (fun x y => _) 0 1.

   Set Printing Existential Instances.

   Check (fun x y => _) 0 1.

Existential variables can be named by the user upon creation using
the syntax :n:`?[@ident]`. This is useful when the existential
variable needs to be explicitly handled later in the script (e.g.
with a named-goal selector, see :ref:`goal-selectors`).

.. _explicit-display-existentials:

Explicit displaying of existential instances for pretty-printing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Existential Instances

   This flag (off by default) activates the full display of how the
   context of an existential variable is instantiated at each of the
   occurrences of the existential variable.

.. _tactics-in-terms:

Solving existential variables using tactics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Instead of letting the unification engine try to solve an existential
variable by itself, one can also provide an explicit hole together
with a tactic to solve it. Using the syntax ``ltac:(``\ `tacexpr`\ ``)``, the user
can put a tactic anywhere a term is expected. The order of resolution
is not specified and is implementation-dependent. The inner tactic may
use any variable defined in its scope, including repeated alternations
between variables introduced by term binding as well as those
introduced by tactic binding. The expression `tacexpr` can be any tactic
expression as described in :ref:`ltac`.

.. coqtop:: all

   Definition foo (x : nat) : nat := ltac:(exact x).

This construction is useful when one wants to define complicated terms
using highly automated tactics without resorting to writing the proof-term
by means of the interactive proof engine.

.. _primitive-integers:

Primitive Integers
------------------

The language of terms features 63-bit machine integers as values. The type of
such a value is *axiomatized*; it is declared through the following sentence
(excerpt from the :g:`Int63` module):

.. coqdoc::

   Primitive int := #int63_type.

This type is equipped with a few operators, that must be similarly declared.
For instance, equality of two primitive integers can be decided using the :g:`Int63.eqb` function,
declared and specified as follows:

.. coqdoc::

   Primitive eqb := #int63_eq.
   Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int63_scope.

   Axiom eqb_correct : forall i j, (i == j)%int63 = true -> i = j.

The complete set of such operators can be obtained looking at the :g:`Int63` module.

These primitive declarations are regular axioms. As such, they must be trusted and are listed by the
:g:`Print Assumptions` command, as in the following example.

.. coqtop:: in reset

   From Coq Require Import Int63.
   Lemma one_minus_one_is_zero : (1 - 1 = 0)%int63.
   Proof. apply eqb_correct; vm_compute; reflexivity. Qed.

.. coqtop:: all

   Print Assumptions one_minus_one_is_zero.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient, rules to reduce the applications of these primitive
operations.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlInt63`
module can be used when extracting to OCaml: it maps the Coq primitives to types
and functions of a :g:`Uint63` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Coq.

Literal values (at type :g:`Int63.int`) are extracted to literal OCaml values
wrapped into the :g:`Uint63.of_int` (resp. :g:`Uint63.of_int64`) constructor on
64-bit (resp. 32-bit) platforms. Currently, this cannot be customized (see the
function :g:`Uint63.compile` from the kernel).

.. _primitive-floats:

Primitive Floats
----------------

The language of terms features Binary64 floating-point numbers as values.
The type of such a value is *axiomatized*; it is declared through the
following sentence (excerpt from the :g:`PrimFloat` module):

.. coqdoc::

   Primitive float := #float64_type.

This type is equipped with a few operators, that must be similarly declared.
For instance, the product of two primitive floats can be computed using the
:g:`PrimFloat.mul` function, declared and specified as follows:

.. coqdoc::

   Primitive mul := #float64_mul.
   Notation "x * y" := (mul x y) : float_scope.

   Axiom mul_spec : forall x y, Prim2SF (x * y)%float = SF64mul (Prim2SF x) (Prim2SF y).

where :g:`Prim2SF` is defined in the :g:`FloatOps` module.

The set of such operators is described in section :ref:`floats_library`.

These primitive declarations are regular axioms. As such, they must be trusted, and are listed by the
:g:`Print Assumptions` command.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient rules to reduce the applications of these primitive
operations, using the floating-point processor operators that are assumed
to comply with the IEEE 754 standard for floating-point arithmetic.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlFloats`
module can be used when extracting to OCaml: it maps the Coq primitives to types
and functions of a :g:`Float64` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Coq.

Literal values (of type :g:`Float64.t`) are extracted to literal OCaml
values (of type :g:`float`) written in hexadecimal notation and
wrapped into the :g:`Float64.of_float` constructor, e.g.:
:g:`Float64.of_float (0x1p+0)`.

.. _bidirectionality_hints:

Bidirectionality hints
----------------------

When type-checking an application, Coq normally does not use information from
the context to infer the types of the arguments. It only checks after the fact
that the type inferred for the application is coherent with the expected type.
Bidirectionality hints make it possible to specify that after type-checking the
first arguments of an application, typing information should be propagated from
the context to help inferring the types of the remaining arguments.

An :cmd:`Arguments` command containing :n:`@argument_spec_block__1 & @argument_spec_block__2`
provides :ref:`bidirectionality_hints`.
It tells the typechecking algorithm, when type-checking
applications of :n:`@qualid`, to first type-check the arguments in
:n:`@argument_spec_block__1` and then propagate information from the typing context to
type-check the remaining arguments (in :n:`@argument_spec_block__2`).

.. example:: Bidirectionality hints

   In a context where a coercion was declared from ``bool`` to ``nat``:

   .. coqtop:: in reset

      Definition b2n (b : bool) := if b then 1 else 0.
      Coercion b2n : bool >-> nat.

   Coq cannot automatically coerce existential statements over ``bool`` to
   statements over ``nat``, because the need for inserting a coercion is known
   only from the expected type of a subterm:

   .. coqtop:: all

      Fail Check (ex_intro _ true _ : exists n : nat, n > 0).

   However, a suitable bidirectionality hint makes the example work:

   .. coqtop:: all

      Arguments ex_intro _ _ & _ _.
      Check (ex_intro _ true _ : exists n : nat, n > 0).

Coq will attempt to produce a term which uses the arguments you
provided, but in some cases involving Program mode the arguments after
the bidirectionality starts may be replaced by convertible but
syntactically different terms.
