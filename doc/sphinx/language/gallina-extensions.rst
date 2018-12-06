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

  .. productionlist:: sentence
     record         : `record_keyword` `record_body` with … with `record_body`
     record_keyword : Record | Inductive | CoInductive
     record_body    : `ident` [ `binders` ] [: `sort` ] := [ `ident` ] { [ `field` ; … ; `field` ] }.
     field          : `ident` [ `binders` ] : `type` [ where `notation` ]
                    : | `ident` [ `binders` ] [: `type` ] := `term`

.. cmd:: Record @ident @binders {? : @sort} := {? @ident} { {*; @ident @binders : @type } }

   The first identifier :token:`ident` is the name of the defined record and :token:`sort` is its
   type. The optional identifier following ``:=`` is the name of its constructor. If it is omitted,
   the default name :n:`Build_@ident`, where :token:`ident` is the record name, is used. If :token:`sort` is
   omitted, the default sort is :math:`\Type`. The identifiers inside the brackets are the names of
   fields. For a given field :token:`ident`, its type is :n:`forall @binders, @type`.
   Remark that the type of a particular identifier may depend on a previously-given identifier. Thus the
   order of the fields is important. Finally, :token:`binders` are parameters of the record.

More generally, a record may have explicitly defined (a.k.a. manifest)
fields. For instance, we might have:
:n:`Record @ident @binders : @sort := { @ident__1 : @type__1 ; @ident__2 := @term__2 ; @ident__3 : @type__3 }`.
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
:n:`Variant @ident {? @binders } : @sort := @ident__0 {? @binders }`.

To build an object of type :token:`ident`, one should provide the constructor
:n:`@ident__0` with the appropriate number of terms filling the fields of the record.

.. example::

   Let us define the rational :math:`1/2`:

    .. coqtop:: in

       Theorem one_two_irred : forall x y z:nat, x * y = 1 /\ x * z = 2 -> x = 1.
       Admitted.

       Definition half := mkRat true 1 2 (O_S 1) one_two_irred.
       Check half.

.. FIXME: move this to the main grammar in the spec chapter

.. _record-named-fields-grammar:

  .. productionlist::
    record_term : {| [`field_def` ; … ; `field_def`] |}
    field_def : name [binders] := `record_term`

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

  .. productionlist:: terms
     projection : `term` `.` ( `qualid` )
          : | `term` `.` ( `qualid` `arg` … `arg` )
          : | `term` `.` ( @`qualid` `term` … `term` )

  Syntax of Record projections

The corresponding grammar rules are given in the preceding grammar. When :token:`qualid`
denotes a projection, the syntax :n:`@term.(@qualid)` is equivalent to :n:`@qualid @term`,
the syntax :n:`@term.(@qualid {+ @arg })` to :n:`@qualid {+ @arg } @term`.
and the syntax :n:`@term.(@@qualid {+ @term })` to :n:`@@qualid {+ @term } @term`.
In each case, :token:`term` is the object projected and the
other arguments are the parameters of the inductive type.


.. note:: Records defined with the ``Record`` keyword are not allowed to be
   recursive (references to the record's name in the type of its field
   raises an  error). To define recursive records, one can use the ``Inductive``
   and ``CoInductive`` keywords, resulting in an inductive or co-inductive record.
   Definition of mutal inductive or co-inductive records are also allowed, as long
   as all of the types in the block are records.

.. note:: Induction schemes are automatically generated for inductive records.
   Automatic generation of induction schemes for non-recursive records
   defined with the ``Record`` keyword can be activated with the
   ``Nonrecursive Elimination Schemes`` option (see :ref:`proofschemes-induction-principles`).

.. note:: ``Structure`` is a synonym of the keyword ``Record``.

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
   Even if the record type has parameters, these do not appear at
   applications of the projection, considerably reducing the sizes of
   terms when manipulating parameterized records and type checking time.
   On the user level, primitive projections can be used as a replacement
   for the usual defined ones, although there are a few notable differences.

.. flag:: Printing Primitive Projection Parameters

   This compatibility option reconstructs internally omitted parameters at
   printing time (even though they are absent in the actual AST manipulated
   by the kernel).

.. flag:: Printing Primitive Projection Compatibility

   This compatibility option (on by default) governs the
   printing of pattern matching over primitive records.

Primitive Record Types
++++++++++++++++++++++

When the :flag:`Primitive Projections` option is on, definitions of
record types change meaning. When a type is declared with primitive
projections, its :g:`match` construct is disabled (see :ref:`primitive_projections` though).
To eliminate the (co-)inductive type, one must use its defined primitive projections.

.. The following paragraph is quite redundant with what is above

For compatibility, the parameters still appear to the user when
printing terms even though they are absent in the actual AST
manipulated by the kernel. This can be changed by unsetting the
:flag:`Printing Primitive Projection Parameters` flag. Further compatibility
printing can be deactivated thanks to the ``Printing Primitive Projection
Compatibility`` option which governs the printing of pattern matching
over primitive records.

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
user-level, and one must use the :flag:`Printing Primitive Projection Compatibility`
to display unfolded primitive projections as matches and distinguish them from folded ones.


Compatibility Projections and :g:`match`
++++++++++++++++++++++++++++++++++++++++

To ease compatibility with ordinary record types, each primitive
projection is also defined as a ordinary constant taking parameters and
an object of the record type as arguments, and whose body is an
application of the unfolded primitive projection of the same name. These
constants are used when elaborating partial applications of the
projection. One can distinguish them from applications of the primitive
projection if the :flag:`Printing Primitive Projection Parameters` option
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

   When this option is on (default), |Coq|’s printer tries to do such
   limited re-factorization.
   Turning it off tells |Coq| to print only simple pattern matching problems
   in the same way as the |Coq| kernel handles them.


Factorization of clauses with same right-hand side
++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Printing Factorizable Match Patterns

   When several patterns share the same right-hand side, it is additionally
   possible to share the clauses using disjunctive patterns. Assuming that the
   printing matching mode is on, this option (on by default) tells |Coq|'s
   printer to try to do this kind of factorization.

Use of a default clause
+++++++++++++++++++++++

.. flag:: Printing Allow Match Default Clause

   When several patterns share the same right-hand side which do not depend on the
   arguments of the patterns, yet an extra factorization is possible: the
   disjunction of patterns can be replaced with a `_` default clause. Assuming that
   the printing matching mode and the factorization mode are on, this option (on by
   default) tells |Coq|'s printer to use a default clause when relevant.

Printing of wildcard patterns
++++++++++++++++++++++++++++++

.. flag:: Printing Wildcard

   Some variables in a pattern may not occur in the right-hand side of
   the pattern matching clause. When this option is on (default), the
   variables having no occurrences in the right-hand side of the
   pattern matching clause are just printed using the wildcard symbol
   “_”.


Printing of the elimination predicate
+++++++++++++++++++++++++++++++++++++

.. flag:: Printing Synth

   In most of the cases, the type of the result of a matched term is
   mechanically synthesizable. Especially, if the result type does not
   depend of the matched term. When this option is on (default),
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

This example emphasizes what the printing options offer.

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

The following experimental command is available when the ``FunInd`` library has been loaded via ``Require Import FunInd``:

.. cmd:: Function @ident {* @binder} { @decrease_annot } : @type := @term

   This command can be seen as a generalization of ``Fixpoint``. It is actually a wrapper
   for several ways of defining a function *and other useful related
   objects*, namely: an induction principle that reflects the recursive
   structure of the function (see :tacn:`function induction`) and its fixpoint equality.
   The meaning of this declaration is to define a function ident,
   similarly to ``Fixpoint``. Like in ``Fixpoint``, the decreasing argument must
   be given (unless the function is not recursive), but it might not
   necessarily be *structurally* decreasing. The point of the {} annotation
   is to name the decreasing argument *and* to describe which kind of
   decreasing criteria must be used to ensure termination of recursive
   calls.

The ``Function`` construction also enjoys the ``with`` extension to define
mutually recursive definitions. However, this feature does not work
for non structurally recursive functions.

See the documentation of functional induction (:tacn:`function induction`)
and ``Functional Scheme`` (:ref:`functional-scheme`) for how to use
the induction principle to easily reason about the function.

Remark: To obtain the right principle, it is better to put rigid
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

.. coqtop:: reset all

   Function plus (n m : nat) {struct n} : nat :=
   match n with
   | 0 => m
   | S p => S (plus p m)
   end.


*Limitations*

|term_0| must be built as a *pure pattern matching tree* (:g:`match … with`)
with applications only *at the end* of each branch.

Function does not support partial application of the function being
defined. Thus, the following example cannot be accepted due to the
presence of partial application of :g:`wrong` in the body of :g:`wrong`:

.. coqtop:: all

   Fail Function wrong (C:nat) : nat :=
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
     which ``Function`` cannot deal with yet.
   - the definition is not a *pattern matching tree* as explained above.

.. warn:: Cannot define principle(s) for @ident.

   The generation of the graph relation (:n:`R_@ident`) succeeded but the induction principle
   could not be built. Only :token:`ident` is defined. Please report.

.. warn:: Cannot build functional inversion principle.

   :tacn:`functional inversion` will not be available for the function.

.. seealso:: :ref:`functional-scheme` and :tacn:`function induction`

Depending on the ``{…}`` annotation, different definition mechanisms are
used by ``Function``. A more precise description is given below.

.. cmdv:: Function @ident {* @binder } : @type := @term

   Defines the not recursive function :token:`ident` as if declared with
   :cmd:`Definition`. Moreover the following are defined:

    + :token:`ident`\ ``_rect``, :token:`ident`\ ``_rec`` and :token:`ident`\ ``_ind``,
      which reflect the pattern matching structure of :token:`term` (see :cmd:`Inductive`);
    + The inductive :n:`R_@ident` corresponding to the graph of :token:`ident` (silently);
    + :token:`ident`\ ``_complete`` and :token:`ident`\ ``_correct`` which
      are inversion information linking the function and its graph.

.. cmdv:: Function @ident {* @binder } { struct @ident } : @type := @term

   Defines the structural recursive function :token:`ident` as if declared
   with :cmd:`Fixpoint`. Moreover the following are defined:

    + The same objects as above;
    + The fixpoint equation of :token:`ident`: :n:`@ident_equation`.

.. cmdv:: Function @ident {* @binder } { measure @term @ident } : @type := @term
          Function @ident {* @binder } { wf @term @ident } : @type := @term

   Defines a recursive function by well-founded recursion. The module ``Recdef``
   of the standard library must be loaded for this feature. The ``{}``
   annotation is mandatory and must be one of the following:

    + :n:`{measure @term @ident }` with :token:`ident` being the decreasing argument
      and :token:`term` being a function from type of :token:`ident` to :g:`nat` for which
      value on the decreasing argument decreases (for the :g:`lt` order on :g:`nat`)
      at each recursive call of :token:`term`. Parameters of the function are
      bound in :token:`term`;
    + :n:`{wf @term @ident }` with :token:`ident` being the decreasing argument and
      :token:`term` an ordering relation on the type of :token:`ident` (i.e. of type
      `T`\ :math:`_{\sf ident}` → `T`\ :math:`_{\sf ident}` → ``Prop``) for which the decreasing argument
      decreases at each recursive call of :token:`term`. The order must be well-founded.
      Parameters of the function are bound in :token:`term`.

   Depending on the annotation, the user is left with some proof
   obligations that will be used to define the function. These proofs
   are: proofs that each recursive call is actually decreasing with
   respect to the given criteria, and (if the criteria is `wf`) a proof
   that the ordering relation is well-founded. Once proof obligations are
   discharged, the following objects are defined:

     + The same objects as with the struct;
     + The lemma `ident`\ :math:`_{\sf tcc}` which collects all proof obligations in one
       property;
     + The lemmas `ident`\ :math:`_{\sf terminate}` and `ident`\ :math:`_{\sf F}` which is needed to be inlined
       during extraction of ident.

   The way this recursive function is defined is the subject of several
   papers by Yves Bertot and Antonia Balaa on the one hand, and Gilles
   Barthe, Julien Forest, David Pichardie, and Vlad Rusu on the other
   hand. Remark: Proof obligations are presented as several subgoals
   belonging to a Lemma `ident`\ :math:`_{\sf tcc}`.

.. _section-mechanism:

Section mechanism
-----------------

The sectioning mechanism can be used to to organize a proof in
structured sections. Then local declarations become available (see
Section :ref:`gallina-definitions`).


.. cmd:: Section @ident

   This command is used to open a section named :token:`ident`.
   Section names do not need to be unique.


.. cmd:: End @ident

   This command closes the section named :token:`ident`. After closing of the
   section, the local declarations (variables and local definitions) get
   *discharged*, meaning that they stop being visible and that all global
   objects defined in the section are generalized with respect to the
   variables and local definitions they each depended on in the section.

   .. example::

      .. coqtop:: all

         Section s1.

         Variables x y : nat.

         Let y' := y.

         Definition x' := S x.

         Definition x'' := x' + y'.

         Print x'.

         End s1.

         Print x'.

         Print x''.

      Notice the difference between the value of :g:`x'` and :g:`x''` inside section
      :g:`s1` and outside.

   .. exn:: This is not the last opened section.
      :undocumented:

.. note::
   Most commands, like :cmd:`Hint`, :cmd:`Notation`, option management, … which
   appear inside a section are canceled when the section is closed.


Module system
-------------

The module system provides a way of packaging related elements
together, as well as a means of massive abstraction.

  .. productionlist:: modules
    module_type       : `qualid`
                      : | `module_type` with Definition `qualid` := `term`
                      : | `module_type` with Module `qualid` := `qualid`
                      : | `qualid` `qualid` … `qualid`
                      : | !`qualid` `qualid` … `qualid`
    module_binding    : ( [Import|Export] `ident` … `ident` : `module_type` )
    module_bindings   : `module_binding` … `module_binding`
    module_expression : `qualid` … `qualid`
                      : | !`qualid` … `qualid`

  Syntax of modules

In the syntax of module application, the ! prefix indicates that any
`Inline` directive in the type of the functor arguments will be ignored
(see the :cmd:`Module Type` command below).


.. cmd:: Module @ident

   This command is used to start an interactive module named :token:`ident`.

.. cmdv:: Module @ident {* @module_binding}

   Starts an interactive functor with
   parameters given by module_bindings.

.. cmdv:: Module @ident : @module_type

   Starts an interactive module specifying its module type.

.. cmdv:: Module @ident {* @module_binding} : @module_type

   Starts an interactive functor with parameters given by the list of
   :token:`module_bindings`, and output module type :token:`module_type`.

.. cmdv:: Module @ident <: {+<: @module_type }

   Starts an interactive module satisfying each :token:`module_type`.

 .. cmdv:: Module @ident {* @module_binding} <: {+<: @module_type }.

   Starts an interactive functor with parameters given by the list of
   :token:`module_binding`. The output module type
   is verified against each :token:`module_type`.

.. cmdv:: Module [ Import | Export ]

   Behaves like :cmd:`Module`, but automatically imports or exports the module.

Reserved commands inside an interactive module
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Include @module

   Includes the content of module in the current
   interactive module. Here module can be a module expression or a module
   type expression. If module is a high-order module or module type
   expression then the system tries to instantiate module by the current
   interactive module.

.. cmd:: Include {+<+ @module}

   is a shortcut for the commands :n:`Include @module` for each :token:`module`.

.. cmd:: End @ident

   This command closes the interactive module :token:`ident`. If the module type
   was given the content of the module is matched against it and an error
   is signaled if the matching fails. If the module is basic (is not a
   functor) its components (constants, inductive types, submodules etc.)
   are now available through the dot notation.

    .. exn:: No such label @ident.
       :undocumented:

    .. exn:: Signature components for label @ident do not match.
       :undocumented:

    .. exn:: This is not the last opened module.
       :undocumented:

.. cmd:: Module @ident := @module_expression

    This command defines the module identifier :token:`ident` to be equal
    to :token:`module_expression`.

    .. cmdv:: Module @ident {* @module_binding} := @module_expression

       Defines a functor with parameters given by the list of :token:`module_binding` and body :token:`module_expression`.

    .. cmdv:: Module @ident {* @module_binding} : @module_type := @module_expression

       Defines a functor with parameters given by the list of :token:`module_binding` (possibly none), and output module type :token:`module_type`,
       with body :token:`module_expression`.

    .. cmdv:: Module @ident {* @module_binding} <: {+<: @module_type} := @module_expression

       Defines a functor with parameters given by module_bindings (possibly none) with body :token:`module_expression`.
       The body is checked against each :n:`@module_type__i`.

    .. cmdv:: Module @ident {* @module_binding} := {+<+ @module_expression}

       is equivalent to an interactive module where each :token:`module_expression` is included.

.. cmd:: Module Type @ident

   This command is used to start an interactive module type :token:`ident`.

   .. cmdv:: Module Type @ident {* @module_binding}

      Starts an interactive functor type with parameters given by :token:`module_bindings`.


Reserved commands inside an interactive module type:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Include @module

   Same as ``Include`` inside a module.

.. cmd:: Include {+<+ @module}

   This is a shortcut for the command :n:`Include @module` for each :token:`module`.

.. cmd:: @assumption_keyword Inline @assums
   :name: Inline

   The instance of this assumption will be automatically expanded at functor application, except when
   this functor application is prefixed by a ``!`` annotation.

.. cmd:: End @ident

   This command closes the interactive module type :token:`ident`.

   .. exn:: This is not the last opened module type.
      :undocumented:

.. cmd:: Module Type @ident := @module_type

   Defines a module type :token:`ident` equal to :token:`module_type`.

    .. cmdv:: Module Type @ident {* @module_binding} := @module_type

       Defines a functor type :token:`ident` specifying functors taking arguments :token:`module_bindings` and
       returning :token:`module_type`.

    .. cmdv:: Module Type @ident {* @module_binding} := {+<+ @module_type }

       is equivalent to an interactive module type were each :token:`module_type` is included.

.. cmd:: Declare Module @ident : @module_type

   Declares a module :token:`ident` of type :token:`module_type`.

    .. cmdv:: Declare Module @ident {* @module_binding} : @module_type

       Declares a functor with parameters given by the list of :token:`module_binding` and output module type
       :token:`module_type`.

.. example::

    Let us define a simple module.

    .. coqtop:: all

       Module M.

       Definition T := nat.

       Definition x := 0.

       Definition y : bool.

       exact true.

       Defined.

       End M.

Inside a module one can define constants, prove theorems and do any
other things that can be done in the toplevel. Components of a closed
module can be accessed using the dot notation:

.. coqtop:: all

   Print M.x.

A simple module type:

.. coqtop:: all

   Module Type SIG.

   Parameter T : Set.

   Parameter x : T.

   End SIG.

Now we can create a new module from M, giving it a less precise
specification: the y component is dropped as well as the body of x.

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

The definition of :g:`N` using the module type expression :g:`SIG` with
:g:`Definition T := nat` is equivalent to the following one:

.. coqtop:: all

   Module Type SIG'.

   Definition T : Set := nat.

   Parameter x : T.

   End SIG'.

   Module N : SIG' := M.

If we just want to be sure that our implementation satisfies a
given module type without restricting the interface, we can use a
transparent constraint

.. coqtop:: all

   Module P <: SIG := M.

   Print P.y.

Now let us create a functor, i.e. a parametric module

.. coqtop:: all

   Module Two (X Y: SIG).

   Definition T := (X.T * Y.T)%type.

   Definition x := (X.x, Y.x).

   End Two.

and apply it to our modules and do some computations:

.. coqtop:: all

   Module Q := Two M N.

   Eval compute in (fst Q.x + snd Q.x).

In the end, let us define a module type with two sub-modules, sharing
some of the fields and give one of its possible implementations:

.. coqtop:: all

   Module Type SIG2.

   Declare Module M1 : SIG.

   Module M2 <: SIG.

   Definition T := M1.T.

   Parameter x : T.

   End M2.

   End SIG2.

   Module Mod <: SIG2.

   Module M1.

   Definition T := nat.

   Definition x := 1.

   End M1.

   Module M2 := M.

   End Mod.

Notice that ``M`` is a correct body for the component ``M2`` since its ``T``
component is equal ``nat`` and hence ``M1.T`` as specified.

.. note::

  #. Modules and module types can be nested components of each other.
  #. One can have sections inside a module or a module type, but not a
     module or a module type inside a section.
  #. Commands like :cmd:`Hint` or :cmd:`Notation` can also appear inside modules and
     module types. Note that in case of a module definition like:

  ::

     Module N : SIG := M.

  or::

    Module N : SIG. … End N.

  hints and the like valid for ``N`` are not those defined in ``M``
  (or the module body) but the ones defined in ``SIG``.


.. _import_qualid:

.. cmd:: Import @qualid

   If :token:`qualid` denotes a valid basic module (i.e. its module type is a
   signature), makes its components available by their short names.

   .. example::

      .. coqtop:: reset all

         Module Mod.

         Definition T:=nat.

         Check T.

         End Mod.

         Check Mod.T.

         Fail Check T.

         Import Mod.

         Check T.

   Some features defined in modules are activated only when a module is
   imported. This is for instance the case of notations (see :ref:`Notations`).

   Declarations made with the ``Local`` flag are never imported by the :cmd:`Import`
   command. Such declarations are only accessible through their fully
   qualified name.

   .. example::

      .. coqtop:: all

         Module A.

         Module B.

         Local Definition T := nat.

         End B.

         End A.

         Import A.

         Fail Check B.T.

   .. cmdv:: Export @qualid
      :name: Export

      When the module containing the command ``Export`` qualid
      is imported, qualid is imported as well.

      .. exn:: @qualid is not a module.
         :undocumented:

      .. warn:: Trying to mask the absolute name @qualid!
         :undocumented:

.. cmd:: Print Module @ident

   Prints the module type and (optionally) the body of the module :token:`ident`.

.. cmd:: Print Module Type @ident

   Prints the module type corresponding to :token:`ident`.

.. flag:: Short Module Printing

   This option (off by default) disables the printing of the types of fields,
   leaving only their names, for the commands :cmd:`Print Module` and
   :cmd:`Print Module Type`.

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
|Coq| name table. Definitions flagged as Local are only accessible with
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

A logical prefix Lib can be associated to a physical pathpath using
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
not unlike the ``Import`` command (see :ref:`here <import_qualid>`). For instance, ``-R`` `path` ``Lib``
associates to the file path `path`\ ``/path/fOO/Bar/File.vo`` the logical name
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

Each implicit argument can be declared to have to be inserted maximally or non
maximally. This can be governed argument per argument by the command
:cmd:`Arguments (implicits)` or globally by the :flag:`Maximal Implicit Insertion` option.

.. seealso:: :ref:`displaying-implicit-args`.


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

In the first setting, one wants to explicitly give the implicit
arguments of a declared object as part of its definition. To do this,
one has to surround the bindings of implicit arguments by curly
braces:

.. coqtop:: all

   Definition id {A : Type} (x : A) : A := x.

This automatically declares the argument A of id as a maximally
inserted implicit argument. One can then do as-if the argument was
absent in every situation but still be able to specify it if needed:

.. coqtop:: all

   Definition compose {A B C} (g : B -> C) (f : A -> B) := fun x => g (f x).

   Goal forall A, compose id id = id (A:=A).


The syntax is supported in all top-level definitions:
:cmd:`Definition`, :cmd:`Fixpoint`, :cmd:`Lemma` and so on. For (co-)inductive datatype
declarations, the semantics are the following: an inductive parameter
declared as an implicit argument need not be repeated in the inductive
definition but will become implicit for the constructors of the
inductive only, not the inductive type itself. For example:

.. coqtop:: all

   Inductive list {A : Type} : Type :=
   | nil : list
   | cons : A -> list -> list.

   Print list.

One can always specify the parameter if it is not uniform using the
usual implicit arguments disambiguation syntax.


Declaring Implicit Arguments
++++++++++++++++++++++++++++



.. cmd:: Arguments @qualid {* [ @ident ] | @ident }
   :name: Arguments (implicits)

   This command is used to set implicit arguments *a posteriori*,
   where the list of possibly bracketed :token:`ident` is a prefix of the list of
   arguments of :token:`qualid` where the ones to be declared implicit are
   surrounded by square brackets and the ones to be declared as maximally
   inserted implicits are surrounded by curly braces.

   After the above declaration is issued, implicit arguments can just
   (and have to) be skipped in any expression involving an application
   of :token:`qualid`.

.. cmd:: Arguments @qualid : clear implicits

   This command clears implicit arguments.

.. cmdv:: Global Arguments @qualid {* [ @ident ] | @ident }

   This command is used to recompute the implicit arguments of
   :token:`qualid` after ending of the current section if any, enforcing the
   implicit arguments known from inside the section to be the ones
   declared by the command.

.. cmdv:: Local Arguments @qualid {* [ @ident ] | @ident }

   When in a module, tell not to activate the
   implicit arguments of :token:`qualid` declared by this command to contexts that
   require the module.

.. cmdv:: {? Global | Local } Arguments @qualid {*, {+ [ @ident ] | @ident } }

   For names of constants, inductive types,
   constructors, lemmas which can only be applied to a fixed number of
   arguments (this excludes for instance constants whose type is
   polymorphic), multiple implicit arguments declarations can be given.
   Depending on the number of arguments qualid is applied to in practice,
   the longest applicable list of implicit arguments is used to select
   which implicit arguments are inserted. For printing, the omitted
   arguments are the ones of the longest list of implicit arguments of
   the sequence.

.. example::

    .. coqtop:: reset all

       Inductive list (A:Type) : Type :=
       | nil : list A
       | cons : A -> list A -> list A.

       Check (cons nat 3 (nil nat)).

       Arguments cons [A] _ _.

       Arguments nil [A].

       Check (cons 3 nil).

       Fixpoint map (A B:Type) (f:A->B) (l:list A) : list B := match l with nil => nil | cons a t => cons (f a) (map A B f t) end.

       Fixpoint length (A:Type) (l:list A) : nat := match l with nil => 0 | cons _ m => S (length A m) end.

       Arguments map [A B] f l.

       Arguments length {A} l. (* A has to be maximally inserted *)

       Check (fun l:list (list nat) => map length l).

       Arguments map [A B] f l, [A] B f l, A B f l.

       Check (fun l => map length l = map (list nat) nat length l).

.. note::
   To know which are the implicit arguments of an object, use the
   command :cmd:`Print Implicit` (see :ref:`displaying-implicit-args`).


Automatic declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Arguments @qualid : default implicits

   This command tells |Coq| to automatically detect what are the implicit arguments of a
   defined object.

   The auto-detection is governed by options telling if strict,
   contextual, or reversible-pattern implicit arguments must be
   considered or not (see :ref:`controlling-strict-implicit-args`, :ref:`controlling-strict-implicit-args`,
   :ref:`controlling-rev-pattern-implicit-args`, and also :ref:`controlling-insertion-implicit-args`).

   .. cmdv:: Global Arguments @qualid : default implicits

      Tell to recompute the
      implicit arguments of qualid after ending of the current section if
      any.

   .. cmdv:: Local Arguments @qualid : default implicits

      When in a module, tell not to activate the implicit arguments of :token:`qualid` computed by this
      declaration to contexts that requires the module.

.. example::

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

.. coqtop:: reset none

   Set Warnings "-local-declaration".

.. coqtop:: all

   Variable X : Type.

   Definition Relation := X -> X -> Prop.

   Definition Transitivity (R:Relation) := forall x y:X, R x y -> forall z:X, R y z -> R x z.

   Variables (R : Relation) (p : Transitivity R).

   Arguments p : default implicits.

   Print p.

   Print Implicit p.

   Variables (a b c : X) (r1 : R a b) (r2 : R b c).

   Check (p r1 r2).


Mode for automatic declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Implicit Arguments

   This option (off by default) allows to systematically declare implicit
   the arguments detectable as such. Auto-detection of implicit arguments is
   governed by options controlling whether strict and contextual implicit
   arguments have to be considered or not.

.. _controlling-strict-implicit-args:

Controlling strict implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Strict Implicit

   When the mode for automatic declaration of implicit arguments is on,
   the default is to automatically set implicit only the strict implicit
   arguments plus, for historical reasons, a small subset of the non-strict
   implicit arguments. To relax this constraint and to set
   implicit all non strict implicit arguments by default, you can turn this
   option off.

.. flag:: Strongly Strict Implicit

   Use this option (off by default) to capture exactly the strict implicit
   arguments and no more than the strict implicit arguments.

.. _controlling-contextual-implicit-args:

Controlling contextual implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Contextual Implicit

   By default, |Coq| does not automatically set implicit the contextual
   implicit arguments. You can turn this option on to tell |Coq| to also
   infer contextual implicit argument.

.. _controlling-rev-pattern-implicit-args:

Controlling reversible-pattern implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Reversible Pattern Implicit

   By default, |Coq| does not automatically set implicit the reversible-pattern
   implicit arguments. You can turn this option on to tell |Coq| to also infer
   reversible-pattern implicit argument.

.. _controlling-insertion-implicit-args:

Controlling the insertion of implicit arguments not followed by explicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Maximal Implicit Insertion

   Assuming the implicit argument mode is on, this option (off by default)
   declares implicit arguments to be automatically inserted when a
   function is partially applied and the next argument of the function is
   an implicit one.

.. _explicit-applications:

Explicit applications
~~~~~~~~~~~~~~~~~~~~~

In presence of non-strict or contextual argument, or in presence of
partial applications, the synthesis of implicit arguments may fail, so
one may have to give explicitly certain implicit arguments of an
application. The syntax for this is :n:`(@ident := @term)` where :token:`ident` is the
name of the implicit argument and term is its corresponding explicit
term. Alternatively, one can locally deactivate the hiding of implicit
arguments of a function by using the notation :n:`@qualid {+ @term }`.
This syntax extension is given in the following grammar:

.. _explicit_app_grammar:

  .. productionlist:: explicit_apps
       term     : @ `qualid` `term` … `term`
                : | @ `qualid`
                : | `qualid` `argument` … `argument`
       argument : `term`
                : | (`ident` := `term`)

  Syntax for explicitly giving implicit arguments

.. example:: (continued)

    .. coqtop:: all

       Check (p r1 (z:=c)).

       Check (p (x:=a) (y:=b) r1 (z:=c) r2).


Renaming implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Arguments @qualid {* @name} : @rename

   This command is used to redefine the names of implicit arguments.

With the assert flag, ``Arguments`` can be used to assert that a given
object has the expected number of arguments and that these arguments
are named as expected.

.. example:: (continued)

   .. coqtop:: all

      Arguments p [s t] _ [u] _: rename.

      Check (p r1 (u:=c)).

      Check (p (s:=a) (t:=b) r1 (u:=c) r2).

      Fail Arguments p [s t] _ [w] _ : assert.

.. _displaying-implicit-args:

Displaying what the implicit arguments are
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Implicit @qualid

   Use this command to display the implicit arguments associated to an object,
   and to know if each of them is to be used maximally or not.


Explicit displaying of implicit arguments for pretty-printing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Implicit

   By default, the basic pretty-printing rules hide the inferable implicit
   arguments of an application. Turn this option on to force printing all
   implicit arguments.

.. flag:: Printing Implicit Defensive

   By default, the basic pretty-printing rules display the implicit
   arguments that are not detected as strict implicit arguments. This
   “defensive” mode can quickly make the display cumbersome so this can
   be deactivated by turning this option off.

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

   Turning this option on (it is off by default) deactivates the use of implicit arguments.

   In this case, all arguments of constants, inductive types,
   constructors, etc, including the arguments declared as implicit, have
   to be given as if no arguments were implicit. By symmetry, this also
   affects printing.

Canonical structures
~~~~~~~~~~~~~~~~~~~~

A canonical structure is an instance of a record/structure type that
can be used to solve unification problems involving a projection
applied to an unknown structure instance (an implicit argument) and a
value. The complete documentation of canonical structures can be found
in :ref:`canonicalstructures`; here only a simple example is given.

.. cmd:: Canonical Structure @qualid

   This command declares :token:`qualid` as a canonical structure.

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

         Canonical Structure nat_setoid.

      Thanks to :g:`nat_setoid` declared as canonical, the implicit arguments :g:`A`
      and :g:`B` can be synthesized in the next statement.

      .. coqtop:: all

         Lemma is_law_S : is_law S.

   .. note::
      If a same field occurs in several canonical structures, then
      only the structure declared first as canonical is considered.

   .. cmdv:: Canonical Structure @ident {? : @type } := @term

      This is equivalent to a regular definition of :token:`ident` followed by the
      declaration :n:`Canonical Structure @ident`.


.. cmd:: Print Canonical Projections

   This displays the list of global names that are components of some
   canonical structure. For each of them, the canonical structure of
   which it is a projection is indicated.

   .. example::

      For instance, the above example gives the following output:

      .. coqtop:: all

         Print Canonical Projections.


Implicit types of variables
~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is possible to bind variable names to a given type (e.g. in a
development using arithmetic, it may be convenient to bind the names :g:`n`
or :g:`m` to the type :g:`nat` of natural numbers).

.. cmd:: Implicit Types {+ @ident } : @type

   The effect of the command is to automatically set the type of bound
   variables starting with :token:`ident` (either :token:`ident` itself or
   :token:`ident` followed by one or more single quotes, underscore or
   digits) to be :token:`type` (unless the bound variable is already declared
   with an explicit type in which case, this latter type is considered).

.. example::

    .. coqtop:: all

       Require Import List.

       Implicit Types m n : nat.

       Lemma cons_inj_nat : forall m n l, n :: l = m :: l -> n = m.

       intros m n.

       Lemma cons_inj_bool : forall (m n:bool) l, n :: l = m :: l -> n = m.

.. cmdv:: Implicit Type @ident : @type

  This is useful for declaring the implicit type of a single variable.

.. cmdv:: Implicit Types {+ ( {+ @ident } : @term ) }

  Adds blocks of implicit types with different specifications.

.. _implicit-generalization:

Implicit generalization
~~~~~~~~~~~~~~~~~~~~~~~

.. index:: `{ }
.. index:: `( )

Implicit generalization is an automatic elaboration of a statement
with free variables into a closed statement where these variables are
quantified explicitly. Implicit generalization is done inside binders
starting with a \` and terms delimited by \`{ } and \`( ), always
introducing maximally inserted implicit arguments for the generalized
variables. Inside implicit generalization delimiters, free variables
in the current context are automatically quantified using a product or
a lambda abstraction to generate a closed term. In the following
statement for example, the variables n and m are automatically
generalized and become explicit arguments of the lemma as we are using
\`( ):

.. coqtop:: all

   Generalizable All Variables.

   Lemma nat_comm : `(n = n + 0).

One can control the set of generalizable identifiers with
the ``Generalizable`` vernacular command to avoid unexpected
generalizations when mistyping identifiers. There are several commands
that specify which variables should be generalizable.

.. cmd:: Generalizable All Variables

   All variables are candidate for
   generalization if they appear free in the context under a
   generalization delimiter. This may result in confusing errors in case
   of typos. In such cases, the context will probably contain some
   unexpected generalized variable.

.. cmd:: Generalizable No Variables

   Disable implicit generalization  entirely. This is the default behavior.

.. cmd:: Generalizable (Variable | Variables) {+ @ident }

   Allow generalization of the given identifiers only. Calling this command multiple times
   adds to the allowed identifiers.

.. cmd:: Global Generalizable

   Allows exporting the choice of generalizable variables.

One can also use implicit generalization for binders, in which case
the generalized variables are added as binders and set maximally
implicit.

.. coqtop:: all

   Definition id `(x : A) : A := x.

   Print id.

The generalizing binders \`{ } and \`( ) work similarly to their
explicit counterparts, only binding the generalized variables
implicitly, as maximally-inserted arguments. In these binders, the
binding name for the bound object is optional, whereas the type is
mandatory, dually to regular binders.

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
   sensitive to the implicit arguments). Turning this option on
   deactivates all high-level printing features such as coercions,
   implicit arguments, returned type of pattern matching, notations and
   various syntactic sugar for pattern matching or record projections.
   Otherwise said, :flag:`Printing All` includes the effects of the options
   :flag:`Printing Implicit`, :flag:`Printing Coercions`, :flag:`Printing Synth`,
   :flag:`Printing Projections`, and :flag:`Printing Notations`. To reactivate
   the high-level printing features, use the command ``Unset Printing All``.

.. _printing-universes:

Printing universes
------------------

.. flag:: Printing Universes

   Turn this option on to activate the display of the actual level of each
   occurrence of :g:`Type`. See :ref:`Sorts` for details. This wizard option, in
   combination with :flag:`Printing All` can help to diagnose failures to unify
   terms apparently identical but internally different in the Calculus of Inductive
   Constructions.

.. cmd:: Print {? Sorted} Universes
   :name: Print Universes

   This command can be used to print the constraints on the internal level
   of the occurrences of :math:`\Type` (see :ref:`Sorts`).

   If the optional ``Sorted`` option is given, each universe will be made
   equivalent to a numbered label reflecting its level (with a linear
   ordering) in the universe hierarchy.

   .. cmdv:: Print {? Sorted} Universes @string

      This variant accepts an optional output filename.

      If :token:`string` ends in ``.dot`` or ``.gv``, the constraints are printed in the DOT
      language, and can be processed by Graphviz tools. The format is
      unspecified if `string` doesn’t end in ``.dot`` or ``.gv``.

.. _existential-variables:

Existential variables
---------------------

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
instantiated by themselves are not written, unless the flag :flag:`Printing Existential Instances`
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

   This option (off by default) activates the full display of how the
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

This mechanism is comparable to the ``Declare Implicit Tactic`` command
defined at :ref:`tactics-implicit-automation`, except that the used
tactic is local to each hole instead of being declared globally.
