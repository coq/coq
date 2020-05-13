Inductive types and recursive functions
=======================================

.. _gallina-inductive-definitions:

Inductive types
---------------

.. cmd:: Inductive @inductive_definition {* with @inductive_definition }

   .. insertprodn inductive_definition constructor

   .. prodn::
      inductive_definition ::= {? > } @ident_decl {* @binder } {? %| {* @binder } } {? : @type } {? := {? @constructors_or_record } } {? @decl_notations }
      constructors_or_record ::= {? %| } {+| @constructor }
      | {? @ident } %{ {*; @record_field } %}
      constructor ::= @ident {* @binder } {? @of_type }

   This command defines one or more
   inductive types and its constructors.  Coq generates destructors
   depending on the universe that the inductive type belongs to.

   The destructors are named :n:`@ident`\ ``_rect``, :n:`@ident`\ ``_ind``,
   :n:`@ident`\ ``_rec`` and :n:`@ident`\ ``_sind``, which
   respectively correspond to elimination principles on :g:`Type`, :g:`Prop`,
   :g:`Set` and :g:`SProp`.  The type of the destructors
   expresses structural induction/recursion principles over objects of
   type :n:`@ident`.  The constant :n:`@ident`\ ``_ind`` is always
   generated, whereas :n:`@ident`\ ``_rec`` and :n:`@ident`\ ``_rect``
   may be impossible to derive (for example, when :n:`@ident` is a
   proposition).

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(monomorphic)`, :attr:`universes(template)`,
   :attr:`universes(notemplate)`, :attr:`universes(cumulative)`,
   :attr:`universes(noncumulative)` and :attr:`private(matching)`
   attributes.

   Mutually inductive types can be defined by including multiple :n:`@inductive_definition`\s.
   The :n:`@ident`\s are simultaneously added to the environment before the types of constructors are checked.
   Each :n:`@ident` can be used independently thereafter.
   See :ref:`mutually_inductive_types`.

   If the entire inductive definition is parameterized with :n:`@binder`\s, the parameters correspond
   to a local context in which the entire set of inductive declarations is interpreted.
   For this reason, the parameters must be strictly the same for each inductive type.
   See :ref:`parametrized-inductive-types`.

   Constructor :n:`@ident`\s can come with :n:`@binder`\s, in which case
   the actual type of the constructor is :n:`forall {* @binder }, @type`.

   .. exn:: Non strictly positive occurrence of @ident in @type.

      The types of the constructors have to satisfy a *positivity condition*
      (see Section :ref:`positivity`). This condition ensures the soundness of
      the inductive definition. The positivity checking can be disabled using
      the :flag:`Positivity Checking` flag (see :ref:`controlling-typing-flags`).

   .. exn:: The conclusion of @type is not valid; it must be built from @ident.

      The conclusion of the type of the constructors must be the inductive type
      :n:`@ident` being defined (or :n:`@ident` applied to arguments in
      the case of annotated inductive types — cf. next section).

The following subsections show examples of simple inductive types,
simple annotated inductive types, simple parametric inductive types,
mutually inductive types and private (matching) inductive types.

.. _simple-inductive-types:

Simple inductive types
~~~~~~~~~~~~~~~~~~~~~~

A simple inductive type belongs to a universe that is a simple :n:`@sort`.

.. example::

   The set of natural numbers is defined as:

   .. coqtop:: reset all

      Inductive nat : Set :=
      | O : nat
      | S : nat -> nat.

   The type nat is defined as the least :g:`Set` containing :g:`O` and closed by
   the :g:`S` constructor. The names :g:`nat`, :g:`O` and :g:`S` are added to the
   environment.

   This definition generates four elimination principles:
   :g:`nat_rect`, :g:`nat_ind`, :g:`nat_rec` and :g:`nat_sind`. The type of :g:`nat_ind` is:

   .. coqtop:: all

      Check nat_ind.

   This is the well known structural induction principle over natural
   numbers, i.e. the second-order form of Peano’s induction principle. It
   allows proving universal properties of natural numbers (:g:`forall
   n:nat, P n`) by induction on :g:`n`.

   The types of :g:`nat_rect`, :g:`nat_rec` and :g:`nat_sind` are similar, except that they
   apply to, respectively, :g:`(P:nat->Type)`, :g:`(P:nat->Set)` and :g:`(P:nat->SProp)`. They correspond to
   primitive induction principles (allowing dependent types) respectively
   over sorts ```Type``, ``Set`` and ``SProp``.

In the case where inductive types don't have annotations (the next section
gives an example of annotations), a constructor can be defined
by giving the type of its arguments alone.

.. example::

   .. coqtop:: reset none

      Reset nat.

   .. coqtop:: in

      Inductive nat : Set := O | S (_:nat).

Simple annotated inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In annotated inductive types, the universe where the inductive type
is defined is no longer a simple :n:`@sort`, but what is called an arity,
which is a type whose conclusion is a :n:`@sort`.

.. example::

   As an example of annotated inductive types, let us define the
   :g:`even` predicate:

   .. coqtop:: all

      Inductive even : nat -> Prop :=
      | even_0 : even O
      | even_SS : forall n:nat, even n -> even (S (S n)).

   The type :g:`nat->Prop` means that :g:`even` is a unary predicate (inductively
   defined) over natural numbers. The type of its two constructors are the
   defining clauses of the predicate :g:`even`. The type of :g:`even_ind` is:

   .. coqtop:: all

      Check even_ind.

   From a mathematical point of view, this asserts that the natural numbers satisfying
   the predicate :g:`even` are exactly in the smallest set of naturals satisfying the
   clauses :g:`even_0` or :g:`even_SS`. This is why, when we want to prove any
   predicate :g:`P` over elements of :g:`even`, it is enough to prove it for :g:`O`
   and to prove that if any natural number :g:`n` satisfies :g:`P` its double
   successor :g:`(S (S n))` satisfies also :g:`P`. This is analogous to the
   structural induction principle we got for :g:`nat`.

.. _parametrized-inductive-types:

Parameterized inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the previous example, each constructor introduces a different
instance of the predicate :g:`even`. In some cases, all the constructors
introduce the same generic instance of the inductive definition, in
which case, instead of an annotation, we use a context of parameters
which are :n:`@binder`\s shared by all the constructors of the definition.

Parameters differ from inductive type annotations in that the
conclusion of each type of constructor invokes the inductive type with
the same parameter values of its specification.

.. example::

   A typical example is the definition of polymorphic lists:

   .. coqtop:: all

      Inductive list (A:Set) : Set :=
      | nil : list A
      | cons : A -> list A -> list A.

   In the type of :g:`nil` and :g:`cons`, we write ":g:`list A`" and not
   just ":g:`list`". The constructors :g:`nil` and :g:`cons` have these types:

   .. coqtop:: all

      Check nil.
      Check cons.

   Observe that the destructors are also quantified with :g:`(A:Set)`, for example:

   .. coqtop:: all

      Check list_ind.

   Once again, the types of the constructor arguments and of the conclusion can be omitted:

   .. coqtop:: none

      Reset list.

   .. coqtop:: in

      Inductive list (A:Set) : Set := nil | cons (_:A) (_:list A).

.. note::
   + The constructor type can
     recursively invoke the inductive definition on an argument which is not
     the parameter itself.

     One can define :

     .. coqtop:: all

        Inductive list2 (A:Set) : Set :=
        | nil2 : list2 A
        | cons2 : A -> list2 (A*A) -> list2 A.

     that can also be written by specifying only the type of the arguments:

     .. coqtop:: all reset

        Inductive list2 (A:Set) : Set :=
        | nil2
        | cons2 (_:A) (_:list2 (A*A)).

     But the following definition will give an error:

     .. coqtop:: all

        Fail Inductive listw (A:Set) : Set :=
        | nilw : listw (A*A)
        | consw : A -> listw (A*A) -> listw (A*A).

     because the conclusion of the type of constructors should be :g:`listw A`
     in both cases.

   + A parameterized inductive definition can be defined using annotations
     instead of parameters but it will sometimes give a different (bigger)
     sort for the inductive definition and will produce a less convenient
     rule for case elimination.

.. flag:: Uniform Inductive Parameters

     When this flag is set (it is off by default),
     inductive definitions are abstracted over their parameters
     before type checking constructors, allowing to write:

     .. coqtop:: all

        Set Uniform Inductive Parameters.
        Inductive list3 (A:Set) : Set :=
        | nil3 : list3
        | cons3 : A -> list3 -> list3.

     This behavior is essentially equivalent to starting a new section
     and using :cmd:`Context` to give the uniform parameters, like so
     (cf. :ref:`section-mechanism`):

     .. coqtop:: all reset

        Section list3.
        Context (A:Set).
        Inductive list3 : Set :=
        | nil3 : list3
        | cons3 : A -> list3 -> list3.
        End list3.

     For finer control, you can use a ``|`` between the uniform and
     the non-uniform parameters:

     .. coqtop:: in reset

        Inductive Acc {A:Type} (R:A->A->Prop) | (x:A) : Prop
          := Acc_in : (forall y, R y x -> Acc y) -> Acc x.

     The flag can then be seen as deciding whether the ``|`` is at the
     beginning (when the flag is unset) or at the end (when it is set)
     of the parameters when not explicitly given.

.. seealso::
   Section :ref:`inductive-definitions` and the :tacn:`induction` tactic.

.. _mutually_inductive_types:

Mutually defined inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. example:: Mutually defined inductive types

   A typical example of mutually inductive data types is trees and
   forests. We assume two types :g:`A` and :g:`B` that are given as variables. The types can
   be declared like this:

   .. coqtop:: in

      Parameters A B : Set.

      Inductive tree : Set := node : A -> forest -> tree

      with forest : Set :=
      | leaf : B -> forest
      | cons : tree -> forest -> forest.

   This declaration automatically generates eight induction principles. They are not the most
   general principles, but they correspond to each inductive part seen as a single inductive definition.

   To illustrate this point on our example, here are the types of :g:`tree_rec`
   and :g:`forest_rec`.

   .. coqtop:: all

      Check tree_rec.

      Check forest_rec.

   Assume we want to parameterize our mutual inductive definitions with the
   two type variables :g:`A` and :g:`B`, the declaration should be
   done as follows:

   .. coqdoc::

      Inductive tree (A B:Set) : Set := node : A -> forest A B -> tree A B

      with forest (A B:Set) : Set :=
      | leaf : B -> forest A B
      | cons : tree A B -> forest A B -> forest A B.

   Assume we define an inductive definition inside a section
   (cf. :ref:`section-mechanism`). When the section is closed, the variables
   declared in the section and occurring free in the declaration are added as
   parameters to the inductive definition.

.. seealso::
   A generic command :cmd:`Scheme` is useful to build automatically various
   mutual induction principles.

.. [1]
   Except if the inductive type is empty in which case there is no
   equation that can be used to infer the return type.

.. index::
   single: fix

Recursive functions: fix
------------------------

.. insertprodn term_fix fixannot

.. prodn::
   term_fix ::= let fix @fix_body in @term
   | fix @fix_body {? {+ with @fix_body } for @ident }
   fix_body ::= @ident {* @binder } {? @fixannot } {? : @type } := @term
   fixannot ::= %{ struct @ident %}
   | %{ wf @one_term @ident %}
   | %{ measure @one_term {? @ident } {? @one_term } %}


The expression ":n:`fix @ident__1 @binder__1 : @type__1 := @term__1 with … with @ident__n @binder__n : @type__n := @term__n for @ident__i`" denotes the
:math:`i`-th component of a block of functions defined by mutual structural
recursion. It is the local counterpart of the :cmd:`Fixpoint` command. When
:math:`n=1`, the ":n:`for @ident__i`" clause is omitted.

The association of a single fixpoint and a local definition have a special
syntax: :n:`let fix @ident {* @binder } := @term in` stands for
:n:`let @ident := fix @ident {* @binder } := @term in`. The same applies for co-fixpoints.

Some options of :n:`@fixannot` are only supported in specific constructs.  :n:`fix` and :n:`let fix`
only support the :n:`struct` option, while :n:`wf` and :n:`measure` are only supported in
commands such as :cmd:`Function` and :cmd:`Program Fixpoint`.

.. _Fixpoint:

Top-level recursive functions
-----------------------------

This section describes the primitive form of definition by recursion over
inductive objects. See the :cmd:`Function` command for more advanced
constructions.

.. cmd:: Fixpoint @fix_definition {* with @fix_definition }

   .. insertprodn fix_definition fix_definition

   .. prodn::
      fix_definition ::= @ident_decl {* @binder } {? @fixannot } {? : @type } {? := @term } {? @decl_notations }

   This command allows defining functions by pattern matching over inductive
   objects using a fixed point construction. The meaning of this declaration is
   to define :n:`@ident` as a recursive function with arguments specified by
   the :n:`@binder`\s such that :n:`@ident` applied to arguments
   corresponding to these :n:`@binder`\s has type :n:`@type`, and is
   equivalent to the expression :n:`@term`. The type of :n:`@ident` is
   consequently :n:`forall {* @binder }, @type` and its value is equivalent
   to :n:`fun {* @binder } => @term`.

   To be accepted, a :cmd:`Fixpoint` definition has to satisfy syntactical
   constraints on a special argument called the decreasing argument. They
   are needed to ensure that the :cmd:`Fixpoint` definition always terminates.
   The point of the :n:`{struct @ident}` annotation (see :n:`@fixannot`) is to
   let the user tell the system which argument decreases along the recursive calls.

   The :n:`{struct @ident}` annotation may be left implicit, in which case the
   system successively tries arguments from left to right until it finds one
   that satisfies the decreasing condition.

   :cmd:`Fixpoint` without the :attr:`program` attribute does not support the
   :n:`wf` or :n:`measure` clauses of :n:`@fixannot`.

   The :n:`with` clause allows simultaneously defining several mutual fixpoints.
   It is especially useful when defining functions over mutually defined
   inductive types.  Example: :ref:`Mutual Fixpoints<example_mutual_fixpoints>`.

   If :n:`@term` is omitted, :n:`@type` is required and Coq enters proof editing mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a constant
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.

   .. note::

      + Some fixpoints may have several arguments that fit as decreasing
        arguments, and this choice influences the reduction of the fixpoint.
        Hence an explicit annotation must be used if the leftmost decreasing
        argument is not the desired one. Writing explicit annotations can also
        speed up type checking of large mutual fixpoints.

      + In order to keep the strong normalization property, the fixed point
        reduction will only be performed when the argument in position of the
        decreasing argument (which type should be in an inductive definition)
        starts with a constructor.


   .. example::

      One can define the addition function as :

      .. coqtop:: all

         Fixpoint add (n m:nat) {struct n} : nat :=
         match n with
         | O => m
         | S p => S (add p m)
         end.

      The match operator matches a value (here :g:`n`) with the various
      constructors of its (inductive) type. The remaining arguments give the
      respective values to be returned, as functions of the parameters of the
      corresponding constructor. Thus here when :g:`n` equals :g:`O` we return
      :g:`m`, and when :g:`n` equals :g:`(S p)` we return :g:`(S (add p m))`.

      The match operator is formally described in
      Section :ref:`match-construction`.
      The system recognizes that in the inductive call :g:`(add p m)` the first
      argument actually decreases because it is a *pattern variable* coming
      from :g:`match n with`.

   .. example::

      The following definition is not correct and generates an error message:

      .. coqtop:: all

         Fail Fixpoint wrongplus (n m:nat) {struct n} : nat :=
         match m with
         | O => n
         | S p => S (wrongplus n p)
         end.

      because the declared decreasing argument :g:`n` does not actually
      decrease in the recursive call. The function computing the addition over
      the second argument should rather be written:

      .. coqtop:: all

         Fixpoint plus (n m:nat) {struct m} : nat :=
         match m with
         | O => n
         | S p => S (plus n p)
         end.

   .. example::

      The recursive call may not only be on direct subterms of the recursive
      variable :g:`n` but also on a deeper subterm and we can directly write
      the function :g:`mod2` which gives the remainder modulo 2 of a natural
      number.

      .. coqtop:: all

         Fixpoint mod2 (n:nat) : nat :=
         match n with
         | O => O
         | S p => match p with
                  | O => S O
                  | S q => mod2 q
                  end
         end.

.. _example_mutual_fixpoints:

   .. example:: Mutual fixpoints

      The size of trees and forests can be defined the following way:

      .. coqtop:: all

         Fixpoint tree_size (t:tree) : nat :=
         match t with
         | node a f => S (forest_size f)
         end
         with forest_size (f:forest) : nat :=
         match f with
         | leaf b => 1
         | cons t f' => (tree_size t + forest_size f')
         end.
