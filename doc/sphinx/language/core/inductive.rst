Inductive types and recursive functions
=======================================

The :cmd:`Inductive` command allows defining types by cases on the form of the
:term:`inhabitants <inhabitant>` of the type. These constructors can recursively
have arguments in the type being defined.  In contrast, in types defined by the
:cmd:`Variant` command, such recursive references are not permitted.
Inductive types include natural numbers,
lists and well-founded trees. Inhabitants of inductive types can
recursively nest only a finite number of constructors. So, they are
well-founded. This distinguishes them from :cmd:`CoInductive` types,
such as streams, whose constructors can be infinitely nested. In Rocq,
:cmd:`Variant` types thus correspond to the common subset of inductive
and coinductive types that are non-recursive.

Due to the recursive structure of inductive types, functions on
inductive types generally must be defined
recursively using the :n:`fix` expression (see :n:`@term_fix`) or the
:cmd:`Fixpoint` command.

.. _gallina-inductive-definitions:

Inductive types
---------------

.. cmd:: Inductive @inductive_definition {* with @inductive_definition }
         Inductive @record_definition {* with @record_definition }

   .. insertprodn inductive_definition constructor

   .. prodn::
      inductive_definition ::= @ident {? @cumul_univ_decl } {* @binder } {? %| {* @binder } } {? : @type } := {? %| } {+| @constructor } {? @decl_notations }
      constructor ::= {* #[ {+, @attribute } ] } @ident {* @binder } {? @of_type_inst }

   Defines one or more
   inductive types and its constructors.  Rocq generates
   :gdef:`induction principles <induction principle>`
   depending on the universe that the inductive type belongs to.

   The induction principles are named :n:`@ident`\ ``_rect``, :n:`@ident`\ ``_ind``,
   :n:`@ident`\ ``_rec`` and :n:`@ident`\ ``_sind``, which
   respectively correspond to
   on :g:`Type`, :g:`Prop`, :g:`Set` and :g:`SProp`.  Their types
   expresses structural induction/recursion principles over objects of
   type :n:`@ident`.  These :term:`constants <constant>` are generated when
   possible (for instance :n:`@ident`\ ``_rect`` may be impossible to derive
   when :n:`@ident` is a proposition).

   .. flag:: Dependent Proposition Eliminators

      The inductive principles express dependent elimination when the
      inductive type allows it (always true when not using
      :flag:`Primitive Projections`), except by default when the
      inductive is explicitly declared in `Prop`.

      Explicitly `Prop` inductive types declared when this flag is
      enabled also automatically declare dependent inductive
      principles. Name generation may also change when using tactics
      such as :tacn:`destruct` on such inductives.

      Note that explicit declarations through :cmd:`Scheme` are not
      affected by this flag.

   :n:`{? %| {* @binder } }`
     The :n:`|` separates uniform and non uniform parameters.
     See :flag:`Uniform Inductive Parameters`.

   The :cmd:`Inductive` command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(template)`, :attr:`universes(cumulative)`,
   :attr:`bypass_check(positivity)`, :attr:`bypass_check(universes)` and
   :attr:`private(matching)` attributes.

   When record syntax is used, this command also supports the
   :attr:`projections(primitive)` :term:`attribute`. Also, in the
   record syntax, if given, the :n:`as @ident` part specifies the name
   to use for inhabitants of the record in the type of projections.

   Mutually inductive types can be defined by including multiple :n:`@inductive_definition`\s.
   The :n:`@ident`\s are simultaneously added to the global environment before
   the types of constructors are checked.  Each :n:`@ident` can be used
   independently thereafter.  However, the induction principles currently generated for
   such types are not useful.  Use the :cmd:`Scheme` command to generate useful
   induction principles.  See :ref:`mutually_inductive_types`.

   If the entire inductive definition is parameterized with :n:`@binder`\s, those
   :gdef:`inductive parameters <inductive parameter>` correspond
   to a local context in which the entire set of inductive declarations is interpreted.
   For this reason, the parameters must be strictly the same for each inductive type.
   See :ref:`parametrized-inductive-types`.

   Constructor :n:`@ident`\s can come with :n:`@binder`\s, in which case
   the actual type of the constructor is :n:`forall {* @binder }, @type`.

   .. exn:: Non strictly positive occurrence of @ident in @type.

      The types of the constructors have to satisfy a *positivity
      condition* (see Section :ref:`positivity`). This condition
      ensures the soundness of the inductive definition.
      Positivity checking can be disabled using the :flag:`Positivity
      Checking` flag or the :attr:`bypass_check(positivity)` attribute (see
      :ref:`controlling-typing-flags`).

   .. exn:: The conclusion of @type is not valid; it must be built from @ident.

      The conclusion of the type of the constructors must be the inductive type
      :n:`@ident` being defined (or :n:`@ident` applied to arguments in
      the case of indexed inductive types — cf. next section).

The following subsections show examples of simple inductive types,
simple indexed inductive types, simple parametric inductive types,
mutually inductive types and private (matching) inductive types.

.. _simple-inductive-types:

Simple inductive types
~~~~~~~~~~~~~~~~~~~~~~

A simple inductive type belongs to a universe that is a simple :n:`@sort`.

.. example::

   The set of natural numbers is defined as:

   .. rocqtop:: reset all

      Inductive nat : Set :=
      | O : nat
      | S : nat -> nat.

   The type nat is defined as the least :g:`Set` containing :g:`O` and closed by
   the :g:`S` constructor. The names :g:`nat`, :g:`O` and :g:`S` are added to the
   global environment.

   This definition generates four :term:`induction principles <induction principle>`:
   :g:`nat_rect`, :g:`nat_ind`, :g:`nat_rec` and :g:`nat_sind`. The type of :g:`nat_ind` is:

   .. rocqtop:: all

      Check nat_ind.

   This is the well known structural induction principle over natural
   numbers, i.e. the second-order form of Peano’s induction principle. It
   allows proving universal properties of natural numbers (:g:`forall
   n:nat, P n`) by induction on :g:`n`.

   The types of :g:`nat_rect`, :g:`nat_rec` and :g:`nat_sind` are similar, except that they
   apply to, respectively, :g:`(P:nat->Type)`, :g:`(P:nat->Set)` and :g:`(P:nat->SProp)`. They correspond to
   primitive induction principles (allowing dependent types) respectively
   over sorts ``Type``, ``Set`` and ``SProp``.

In the case where inductive types don't have indices (the next section
gives an example of indices), a constructor can be defined
by giving the type of its arguments alone.

.. example::

   .. rocqtop:: reset none

      Reset nat.

   .. rocqtop:: in

      Inductive nat : Set := O | S (_:nat).

Automatic Prop lowering
+++++++++++++++++++++++

When an inductive is declared without an explicit sort, it is put in the
smallest sort which permits large elimination (excluding
`SProp`). For :ref:`empty and singleton <Empty-and-singleton-elimination>`
types this means they are declared in `Prop`.

Simple indexed inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In indexed inductive types, the universe where the inductive type
is defined is no longer a simple :n:`@sort`, but what is called an arity,
which is a type whose conclusion is a :n:`@sort`.

.. example::

   As an example of indexed inductive types, let us define the
   :g:`even` predicate:

   .. rocqtop:: all

      Inductive even : nat -> Prop :=
      | even_0 : even O
      | even_SS : forall n:nat, even n -> even (S (S n)).

   The type :g:`nat->Prop` means that :g:`even` is a unary predicate (inductively
   defined) over natural numbers. The type of its two constructors are the
   defining clauses of the predicate :g:`even`. The type of :g:`even_ind` is:

   .. rocqtop:: all

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
which case, instead of an index, we use a context of parameters
which are :n:`@binder`\s shared by all the constructors of the definition.

Parameters differ from inductive type indices in that the
conclusion of each type of constructor invokes the inductive type with
the same parameter values of its specification.

.. example::

   A typical example is the definition of polymorphic lists:

   .. rocqtop:: all

      Inductive list (A:Set) : Set :=
      | nil : list A
      | cons : A -> list A -> list A.

   In the type of :g:`nil` and :g:`cons`, we write ":g:`list A`" and not
   just ":g:`list`". The constructors :g:`nil` and :g:`cons` have these types:

   .. rocqtop:: all

      Check nil.
      Check cons.

   Observe that the induction principles are also quantified with :g:`(A:Set)`,
   for example:

   .. rocqtop:: all

      Check list_ind.

   Once again, the names of the constructor arguments and the type of the conclusion can be omitted:

   .. rocqtop:: none

      Reset list.

   .. rocqtop:: in

      Inductive list (A:Set) : Set := nil | cons (_:A) (_:list A).

.. note::
   + The constructor type can
     recursively invoke the inductive definition on an argument which is not
     the parameter itself.

     One can define :

     .. rocqtop:: all

        Inductive list2 (A:Set) : Set :=
        | nil2 : list2 A
        | cons2 : A -> list2 (A*A) -> list2 A.

     that can also be written by specifying only the type of the arguments:

     .. rocqtop:: all reset

        Inductive list2 (A:Set) : Set :=
        | nil2
        | cons2 (_:A) (_:list2 (A*A)).

     But the following definition will give an error:

     .. rocqtop:: all

        Fail Inductive listw (A:Set) : Set :=
        | nilw : listw (A*A)
        | consw : A -> listw (A*A) -> listw (A*A).

     because the conclusion of the type of constructors should be :g:`listw A`
     in both cases.

   + A parameterized inductive definition can be defined using indices
     instead of parameters but it will sometimes give a different (bigger)
     sort for the inductive definition and will produce a less convenient
     rule for case elimination.

.. flag:: Uniform Inductive Parameters

     When this :term:`flag` is set (it is off by default),
     inductive definitions are abstracted over their parameters
     before type checking constructors, allowing to write:

     .. rocqtop:: all

        Set Uniform Inductive Parameters.
        Inductive list3 (A:Set) : Set :=
        | nil3 : list3
        | cons3 : A -> list3 -> list3.

     This behavior is essentially equivalent to starting a new section
     and using :cmd:`Context` to give the uniform parameters, like so
     (cf. :ref:`section-mechanism`):

     .. rocqtop:: all reset

        Section list3.
        Context (A:Set).
        Inductive list3 : Set :=
        | nil3 : list3
        | cons3 : A -> list3 -> list3.
        End list3.

     For finer control, you can use a ``|`` between the uniform and
     the non-uniform parameters:

     .. rocqtop:: in reset

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

.. todo: combine with the very similar tree/forest example in reasoning-inductives.rst

The induction principles currently generated for mutually defined types are not
useful.  Use the :cmd:`Scheme` command to generate a useful induction principle.

.. example:: Mutually defined inductive types

   A typical example of mutually inductive data types is trees and
   forests. We assume two types :g:`A` and :g:`B` that are given as variables. The types can
   be declared like this:

   .. rocqtop:: in

      Parameters A B : Set.

      Inductive tree : Set := node : A -> forest -> tree

      with forest : Set :=
      | leaf : B -> forest
      | cons : tree -> forest -> forest.

   This declaration automatically generates eight induction principles. They are not the most
   general principles, but they correspond to each inductive part seen as a single inductive definition.

   To illustrate this point on our example, here are the types of :g:`tree_rec`
   and :g:`forest_rec`.

   .. rocqtop:: all

      Check tree_rec.

      Check forest_rec.

   Assume we want to parameterize our mutual inductive definitions with the
   two type variables :g:`A` and :g:`B`, the declaration should be
   done as follows:

   .. rocqdoc::

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

.. index::
   single: fix

Recursive functions: fix
------------------------

.. insertprodn term_fix fixannot

.. prodn::
   term_fix ::= let fix @fix_decl in @term
   | fix @fix_decl {? {+ with @fix_decl } for @ident }
   fix_decl ::= @ident {* @binder } {? @fixannot } {? : @type } := @term
   fixannot ::= %{ struct @ident %}
   | %{ wf @one_term @ident %}
   | %{ measure @one_term {? @ident } {? @one_term } %}


The expression ":n:`fix @ident__1 @binder__1 : @type__1 := @term__1 with … with @ident__n @binder__n : @type__n := @term__n for @ident__i`" denotes the
:math:`i`-th component of a block of functions defined by mutual structural
recursion. It is the local counterpart of the :cmd:`Fixpoint` command. When
:math:`n=1`, the ":n:`for @ident__i`" clause is omitted.

The association of a single fixpoint and a local definition have a special
syntax: :n:`let fix @ident {* @binder } := @term in` stands for
:n:`let @ident := fix @ident {* @binder } := @term in`. The same applies for cofixpoints.

Some options of :n:`@fixannot` are only supported in specific constructs.  :n:`fix` and :n:`let fix`
only support the :n:`struct` option, while :n:`wf` and :n:`measure` are only supported in
commands such as :cmd:`Fixpoint` (with the :attr:`program` attribute) and :cmd:`Function`.

.. todo explanation of struct: see text above at the Fixpoint command, also
   see https://github.com/coq/coq/pull/12936#discussion_r510716268 and above.
   Consider whether to move the grammar for fixannot elsewhere

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

   Allows defining functions by pattern matching over inductive
   objects using a fixed point construction. The meaning of this declaration is
   to define :n:`@ident` as a recursive function with arguments specified by
   the :n:`@binder`\s such that :n:`@ident` applied to arguments
   corresponding to these :n:`@binder`\s has type :n:`@type`, and is
   equivalent to the expression :n:`@term`. The type of :n:`@ident` is
   consequently :n:`forall {* @binder }, @type` and its value is equivalent
   to :n:`fun {* @binder } => @term`.

   This command accepts the :attr:`program`,
   :attr:`bypass_check(universes)`, and :attr:`bypass_check(guard)` attributes.

   To be accepted, a :cmd:`Fixpoint` definition has to satisfy syntactical
   constraints on a special argument called the decreasing argument. They
   are needed to ensure that the :cmd:`Fixpoint` definition always terminates.
   The point of the :n:`{struct @ident}` annotation (see :n:`@fixannot`) is to
   let the user tell the system which argument decreases along the recursive calls.

   The :n:`{struct @ident}` annotation may be left implicit, in which case the
   system successively tries arguments from left to right until it finds one
   that satisfies the decreasing condition.

   :cmd:`Fixpoint` without the :attr:`program` attribute does not support the
   :n:`wf` or :n:`measure` clauses of :n:`@fixannot`. See :ref:`program_fixpoint`.

   The :n:`with` clause allows simultaneously defining several mutual fixpoints.
   It is especially useful when defining functions over mutually defined
   inductive types.  Example: :ref:`Mutual Fixpoints<example_mutual_fixpoints>`.

   If :n:`@term` is omitted, :n:`@type` is required and Rocq enters proof mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a :term:`constant`
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.

   This command accepts the :attr:`using` attribute.

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

      .. rocqtop:: all

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

      .. rocqtop:: all

         Fail Fixpoint wrongplus (n m:nat) {struct n} : nat :=
         match m with
         | O => n
         | S p => S (wrongplus n p)
         end.

      because the declared decreasing argument :g:`n` does not actually
      decrease in the recursive call.

      .. _reversed_add_example:

      The function computing the addition over the second argument should rather be written:

      .. rocqtop:: all

         Fixpoint plus (n m:nat) {struct m} : nat :=
         match m with
         | O => n
         | S p => S (plus n p)
         end.

      **Aside**: Observe that `plus n 0` is reducible but `plus 0 n` is not,
      the reverse of `Nat.add`, for which `0 + n` is reducible and `n + 0` is not.

      .. rocqtop:: all

         Goal forall n:nat, plus n 0 = plus 0 n.
         intros; simpl.  (* plus 0 n not reducible *)

      .. rocqtop:: none

         Abort.

      .. rocqtop:: all

         Goal forall n:nat, n + 0 = 0 + n.
         intros; simpl.  (* n + 0 not reducible *)

      .. rocqtop:: none

         Abort.

   .. example::

      The recursive call may not only be on direct subterms of the recursive
      variable :g:`n` but also on a deeper subterm and we can directly write
      the function :g:`mod2` which gives the remainder modulo 2 of a natural
      number.

      .. rocqtop:: all

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

      .. rocqtop:: all

         Fixpoint tree_size (t:tree) : nat :=
         match t with
         | node a f => S (forest_size f)
         end
         with forest_size (f:forest) : nat :=
         match f with
         | leaf b => 1
         | cons t f' => (tree_size t + forest_size f')
         end.

.. extracted from CIC chapter

.. _inductive-definitions:

Theory of inductive definitions
-------------------------------

Formally, we can represent any *inductive definition* as
:math:`\ind{p}{Γ_I}{Γ_C}` where:

+ :math:`Γ_I` determines the names and types of inductive types;
+ :math:`Γ_C` determines the names and types of constructors of these
  inductive types;
+ :math:`p` determines the number of parameters of these inductive types.


These inductive definitions, together with global assumptions and
global definitions, then form the global environment. Additionally,
for any :math:`p` there always exists :math:`Γ_P =[a_1 :A_1 ;~…;~a_p :A_p ]` such that
each :math:`T` in :math:`(t:T)∈Γ_I \cup Γ_C` can be written as: :math:`∀Γ_P , T'` where :math:`Γ_P` is
called the *context of parameters*. Furthermore, we must have that
each :math:`T` in :math:`(t:T)∈Γ_I` can be written as: :math:`∀Γ_P,∀Γ_{\mathit{Arr}(t)}, S` where
:math:`Γ_{\mathit{Arr}(t)}` is called the *Arity* of the inductive type :math:`t` and :math:`S` is called
the sort of the inductive type :math:`t` (not to be confused with :math:`\Sort` which is the set of sorts).

.. example::

   The declaration for parameterized lists is:

   .. math::
      \ind{1}{[\List:\Set→\Set]}{\left[\begin{array}{rcl}
      \Nil & : & ∀ A:\Set,~\List~A \\
      \cons & : & ∀ A:\Set,~A→ \List~A→ \List~A
      \end{array}
      \right]}

   which corresponds to the result of the Rocq declaration:

   .. rocqtop:: in reset

      Inductive list (A:Set) : Set :=
      | nil : list A
      | cons : A -> list A -> list A.

.. example::

   The declaration for a mutual inductive definition of tree and forest
   is:

   .. math::
      \ind{0}{\left[\begin{array}{rcl}\tree&:&\Set\\\forest&:&\Set\end{array}\right]}
       {\left[\begin{array}{rcl}
                \node &:& \forest → \tree\\
                \emptyf &:& \forest\\
                \consf &:& \tree → \forest → \forest\\
                          \end{array}\right]}

   which corresponds to the result of the Rocq declaration:

   .. rocqtop:: in

      Inductive tree : Set :=
      | node : forest -> tree
      with forest : Set :=
      | emptyf : forest
      | consf : tree -> forest -> forest.

.. example::

   The declaration for a mutual inductive definition of even and odd is:

   .. math::
      \ind{0}{\left[\begin{array}{rcl}\even&:&\nat → \Prop \\
                                      \odd&:&\nat → \Prop \end{array}\right]}
       {\left[\begin{array}{rcl}
                \evenO &:& \even~0\\
                \evenS &:& ∀ n,~\odd~n → \even~(\nS~n)\\
                \oddS &:& ∀ n,~\even~n → \odd~(\nS~n)
                          \end{array}\right]}

   which corresponds to the result of the Rocq declaration:

   .. rocqtop:: in

      Inductive even : nat -> Prop :=
      | even_O : even 0
      | even_S : forall n, odd n -> even (S n)
      with odd : nat -> Prop :=
      | odd_S : forall n, even n -> odd (S n).



.. _Types-of-inductive-objects:

Types of inductive objects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We have to give the type of constants in a global environment :math:`E` which
contains an inductive definition.

.. inference:: Ind

   \WFE{Γ}
   \ind{p}{Γ_I}{Γ_C} ∈ E
   (a:A)∈Γ_I
   ---------------------
   E[Γ] ⊢ a : A

.. inference:: Constr

   \WFE{Γ}
   \ind{p}{Γ_I}{Γ_C} ∈ E
   (c:C)∈Γ_C
   ---------------------
   E[Γ] ⊢ c : C

.. example::

   Provided that our global environment :math:`E` contains inductive definitions we showed before,
   these two inference rules above enable us to conclude that:

   .. math::
      \begin{array}{l}
      E[Γ] ⊢ \even : \nat→\Prop\\
      E[Γ] ⊢ \odd : \nat→\Prop\\
      E[Γ] ⊢ \evenO : \even~\nO\\
      E[Γ] ⊢ \evenS : ∀ n:\nat,~\odd~n → \even~(\nS~n)\\
      E[Γ] ⊢ \oddS : ∀ n:\nat,~\even~n → \odd~(\nS~n)
      \end{array}




.. _Well-formed-inductive-definitions:

Well-formed inductive definitions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We cannot accept any inductive definition because some of them lead
to inconsistent systems. We restrict ourselves to definitions which
satisfy a syntactic criterion of positivity. Before giving the formal
rules, we need a few definitions:

Arity of a given sort
+++++++++++++++++++++

A type :math:`T` is an *arity of sort* :math:`s` if it converts to the sort :math:`s` or to a
product :math:`∀ x:T,~U` with :math:`U` an arity of sort :math:`s`.

.. example::

   :math:`A→\Set` is an arity of sort :math:`\Set`. :math:`∀ A:\Prop,~A→ \Prop` is an arity of sort
   :math:`\Prop`.


Arity
+++++
A type :math:`T` is an *arity* if there is a :math:`s∈ \Sort` such that :math:`T` is an arity of
sort :math:`s`.


.. example::

   :math:`A→ \Set` and :math:`∀ A:\Prop,~A→ \Prop` are arities.

..
   Convention in describing inductive types:
   k is the number of inductive types (I_i : forall params, A_i)
   n is the number of constructors in the whole block (c_i : forall params, C_i)
   r is the number of parameters
   l is the size of the context of parameters (p_i : P_i)
   m is the number of recursively non-uniform parameters among parameters
   s is the number of indices
   q = r+s is the number of parameters and indices


Type of constructor
+++++++++++++++++++
We say that :math:`T` is a *type of constructor of* :math:`I` in one of the following
two cases:

+ :math:`T` is :math:`(I~t_1 … t_q )`
+ :math:`T` is :math:`∀ x:U,~T'` where :math:`T'` is also a type of constructor of :math:`I`

.. example::

   :math:`\nat` and :math:`\nat→\nat` are types of constructor of :math:`\nat`.
   :math:`∀ A:\Type,~\List~A` and :math:`∀ A:\Type,~A→\List~A→\List~A` are types of constructor of :math:`\List`.

.. _positivity:

Positivity Condition
++++++++++++++++++++

The type of constructor :math:`T` will be said to *satisfy the positivity
condition* for a set of constants :math:`X_1 … X_k` in the following cases:

+ :math:`T=(X_j~t_1 … t_q )` for some :math:`j` and no :math:`X_1 … X_k` occur free in any :math:`t_i`
+ :math:`T=∀ x:U,~V` and :math:`X_1 … X_k` occur only strictly positively in :math:`U` and the type :math:`V`
  satisfies the positivity condition for :math:`X_1 … X_k`.

Strict positivity
+++++++++++++++++

The constants :math:`X_1 … X_k` *occur strictly positively* in :math:`T` in the following
cases:


+ no :math:`X_1 … X_k` occur in :math:`T`
+ :math:`T` converts to :math:`(X_j~t_1 … t_q )` for some :math:`j` and no :math:`X_1 … X_k` occur in any of :math:`t_i`
+ :math:`T` converts to :math:`∀ x:U,~V` and :math:`X_1 … X_k` occur
  strictly positively in type :math:`V` but none of them occur in :math:`U`
+ :math:`T` converts to :math:`(I~a_1 … a_r~t_1 … t_s )` where :math:`I` is the name of an
  inductive definition of the form

  .. math::
     \ind{r}{I:A}{c_1 :∀ p_1 :P_1 ,… ∀p_r :P_r ,~C_1 ;~…;~c_n :∀ p_1 :P_1 ,… ∀p_r :P_r ,~C_n}

  (in particular, it is
  not mutually defined and it has :math:`r` parameters) and no :math:`X_1 … X_k` occur in
  any of the :math:`t_i` nor in any of the :math:`a_j` for :math:`m < j ≤ r` where :math:`m ≤ r`
  is the number of recursively uniform parameters, and the (instantiated) types of constructor
  :math:`\subst{C_i}{p_j}{a_j}_{j=1… m}` of :math:`I` satisfy the nested positivity condition for :math:`X_1 … X_k`

Nested Positivity
+++++++++++++++++

If :math:`I` is a non-mutual inductive type with :math:`r`
parameters, then,
the type of constructor :math:`T` of :math:`I` *satisfies the nested
positivity condition* for a set of constants :math:`X_1 … X_k` in the following
cases:

+ :math:`T=(I~b_1 … b_r~u_1 … u_s)` and no :math:`X_1 … X_k` occur in
  any :math:`u_i` nor in
  any of the :math:`b_j` for :math:`m < j ≤ r` where :math:`m ≤ r` is
  the number of recursively uniform parameters

+ :math:`T=∀ x:U,~V` and :math:`X_1 … X_k` occur only strictly positively in :math:`U` and the type :math:`V`
  satisfies the nested positivity condition for :math:`X_1 … X_k`


.. example::

   For instance, if one considers the following variant of a tree type
   branching over the natural numbers:

   .. rocqtop:: in

      Inductive nattree (A:Type) : Type :=
      | leaf : nattree A
      | natnode : A -> (nat -> nattree A) -> nattree A.

   Then every instantiated constructor of ``nattree A`` satisfies the nested positivity
   condition for ``nattree``:

   + Type ``nattree A`` of constructor ``leaf`` satisfies the positivity condition for
     ``nattree`` because ``nattree`` does not appear in any (real) arguments of the
     type of that constructor (primarily because ``nattree`` does not have any (real)
     arguments) ... (bullet 1)

   + Type ``A → (nat → nattree A) → nattree A`` of constructor ``natnode`` satisfies the
     positivity condition for ``nattree`` because:

     - ``nattree`` occurs only strictly positively in ``A`` ... (bullet 1)

     - ``nattree`` occurs only strictly positively in ``nat → nattree A`` ... (bullet 3 + 2)

     - ``nattree`` satisfies the positivity condition for ``nattree A`` ... (bullet 1)

.. _Correctness-rules:

Correctness rules
+++++++++++++++++

We shall now describe the rules allowing the introduction of a new
inductive definition.

Let :math:`E` be a global environment and :math:`Γ_P`, :math:`Γ_I`, :math:`Γ_C` be contexts
such that :math:`Γ_I` is :math:`[I_1 :∀ Γ_P ,A_1 ;~…;~I_k :∀ Γ_P ,A_k]`, and
:math:`Γ_C` is :math:`[c_1:∀ Γ_P ,C_1 ;~…;~c_n :∀ Γ_P ,C_n ]`. Then

.. inference:: W-Ind

   \WFE{Γ_P}
   (E[Γ_I ;Γ_P ] ⊢ C_i : s_{q_i} )_{i=1… n}
   ------------------------------------------
   \WF{E;~\ind{l}{Γ_I}{Γ_C}}{}


provided that the following side conditions hold:

    + :math:`k>0` and all of :math:`I_j` and :math:`c_i` are distinct names for :math:`j=1… k` and :math:`i=1… n`,
    + :math:`l` is the size of :math:`Γ_P` which is called the context of parameters,
    + for :math:`j=1… k` we have that :math:`A_j` is an arity of sort :math:`s_j` and :math:`I_j ∉ E`,
    + for :math:`i=1… n` we have that :math:`C_i` is a type of constructor of :math:`I_{q_i}` which
      satisfies the positivity condition for :math:`I_1 … I_k` and :math:`c_i ∉  E`.

One can remark that there is a constraint between the sort of the
arity of the inductive type and the sort of the type of its
constructors which will always be satisfied for the impredicative
sorts :math:`\SProp` and :math:`\Prop` but may fail to define
inductive type on sort :math:`\Set` and generate constraints
between universes for inductive types in the Type hierarchy.


.. example::

   It is well known that the existential quantifier can be encoded as an
   inductive definition. The following declaration introduces the
   second-order existential quantifier :math:`∃ X.P(X)`.

   .. rocqtop:: in

      Inductive exProp (P:Prop->Prop) : Prop :=
      | exP_intro : forall X:Prop, P X -> exProp P.

   The same definition on :math:`\Set` is not allowed and fails:

   .. rocqtop:: all

      Fail Inductive exSet (P:Set->Prop) : Set :=
      exS_intro : forall X:Set, P X -> exSet P.

   It is possible to declare the same inductive definition in the
   universe :math:`\Type`. The :g:`exType` inductive definition has type
   :math:`(\Type(i)→\Prop)→\Type(j)` with the constraint that the parameter :math:`X` of :math:`\kw{exT}_{\kw{intro}}`
   has type :math:`\Type(k)` with :math:`k<j` and :math:`k≤ i`.

   .. rocqtop:: all

      Inductive exType (P:Type->Prop) : Type :=
      exT_intro : forall X:Type, P X -> exType P.


.. example:: Negative occurrence (first example)

   The following inductive definition is rejected because it does not
   satisfy the positivity condition:

   .. rocqtop:: all

      Fail Inductive I : Prop := not_I_I (not_I : I -> False) : I.

   If we were to accept such definition, we could derive a
   contradiction from it (we can test this by disabling the
   :flag:`Positivity Checking` flag):

   .. rocqtop:: in

      #[bypass_check(positivity)] Inductive I : Prop := not_I_I (not_I : I -> False) : I.

   .. rocqtop:: all

      Definition I_not_I : I -> ~ I := fun i =>
        match i with not_I_I not_I => not_I end.

   .. rocqtop:: in

      Lemma contradiction : False.
      Proof.
        enough (I /\ ~ I) as [] by contradiction.
        split.
        - apply not_I_I.
          intro.
          now apply I_not_I.
        - intro.
          now apply I_not_I.
      Qed.

.. example:: Negative occurrence (second example)

   Here is another example of an inductive definition which is
   rejected because it does not satify the positivity condition:

   .. rocqtop:: all

      Fail Inductive Lam := lam (_ : Lam -> Lam).

   Again, if we were to accept it, we could derive a contradiction
   (this time through a non-terminating recursive function):

   .. rocqtop:: in

      #[bypass_check(positivity)] Inductive Lam := lam (_ : Lam -> Lam).

   .. rocqtop:: all

      Fixpoint infinite_loop l : False :=
        match l with lam x => infinite_loop (x l) end.

      Check infinite_loop (lam (@id Lam)) : False.

.. example:: Non strictly positive occurrence

   It is less obvious why inductive type definitions with occurences
   that are positive but not strictly positive are harmful.
   We will see that in presence of an impredicative type they
   are unsound:

   .. rocqtop:: all

      Fail Inductive A: Type := introA: ((A -> Prop) -> Prop) -> A.

   If we were to accept this definition we could derive a contradiction
   by creating an injective function from :math:`A → \Prop` to :math:`A`.

   This function is defined by composing the injective constructor of
   the type :math:`A` with the function :math:`λx. λz. z = x` injecting
   any type :math:`T` into :math:`T → \Prop`.

   .. rocqtop:: in

      #[bypass_check(positivity)] Inductive A: Type := introA: ((A -> Prop) -> Prop) -> A.

   .. rocqtop:: all

      Definition f (x: A -> Prop): A := introA (fun z => z = x).

   .. rocqtop:: in

      Lemma f_inj: forall x y, f x = f y -> x = y.
      Proof.
        unfold f; intros ? ? H; injection H.
        set (F := fun z => z = y); intro HF.
        symmetry; replace (y = x) with (F y).
        + unfold F; reflexivity.
        + rewrite <- HF; reflexivity.
      Qed.

   The type :math:`A → \Prop` can be understood as the powerset
   of the type :math:`A`. To derive a contradiction from the
   injective function :math:`f` we use Cantor's classic diagonal
   argument.

   .. rocqtop:: all

      Definition d: A -> Prop := fun x => exists s, x = f s /\ ~s x.
      Definition fd: A := f d.

   .. rocqtop:: in

      Lemma cantor: (d fd) <-> ~(d fd).
      Proof.
        split.
        + intros [s [H1 H2]]; unfold fd in H1.
          replace d with s.
          * assumption.
          * apply f_inj; congruence.
        + intro; exists d; tauto.
      Qed.

      Lemma bad: False.
      Proof.
        pose cantor; tauto.
      Qed.

   This derivation was first presented by Thierry Coquand and Christine
   Paulin in :cite:`CP90`.

.. _Template-polymorphism:

Template polymorphism
+++++++++++++++++++++

Inductive types can be made polymorphic over the universes introduced by
their parameters in :math:`\Type`, if the minimal inferred sort of the
inductive declarations either mention some of those parameter universes
or is computed to be :math:`\Prop` or :math:`\Set`.

If :math:`A` is an arity of some sort and :math:`s` is a sort, we write :math:`A_{/s}`
for the arity obtained from :math:`A` by replacing its sort with :math:`s`.
Especially, if :math:`A` is well-typed in some global environment and local
context, then :math:`A_{/s}` is typable by typability of all products in the
Calculus of Inductive Constructions. The following typing rule is
added to the theory.

Let :math:`\ind{p}{Γ_I}{Γ_C}` be an inductive definition. Let
:math:`Γ_P = [p_1 :P_1 ;~…;~p_p :P_p ]` be its context of parameters,
:math:`Γ_I = [I_1:∀ Γ_P ,A_1 ;~…;~I_k :∀ Γ_P ,A_k ]` its context of definitions and
:math:`Γ_C = [c_1 :∀ Γ_P ,C_1 ;~…;~c_n :∀ Γ_P ,C_n]` its context of constructors,
with :math:`c_i` a constructor of :math:`I_{q_i}`. Let :math:`m ≤ p` be the length of the
longest prefix of parameters such that the :math:`m` first arguments of all
occurrences of all :math:`I_j` in all :math:`C_k` (even the occurrences in the
hypotheses of :math:`C_k`) are exactly applied to :math:`p_1 … p_m` (:math:`m` is the number
of *recursively uniform parameters* and the :math:`p−m` remaining parameters
are the *recursively non-uniform parameters*). Let :math:`q_1 , …, q_r`, with
:math:`0≤ r≤ m`, be a (possibly) partial instantiation of the recursively
uniform parameters of :math:`Γ_P`. We have:

.. inference:: Ind-Family

   \left\{\begin{array}{l}
   \ind{p}{Γ_I}{Γ_C} \in E\\
   (E[]  ⊢ q_l : P'_l)_{l=1\ldots r}\\
   (E[]  ⊢ P'_l ≤_{βδιζη} \subst{P_l}{p_u}{q_u}_{u=1\ldots l-1})_{l=1\ldots r}\\
   1 \leq j \leq k
   \end{array}
   \right.
   -----------------------------
   E[] ⊢ I_j~q_1 … q_r :∀ [p_{r+1} :P_{r+1} ;~…;~p_p :P_p], (A_j)_{/s_j}

provided that the following side conditions hold:

    + :math:`Γ_{P′}` is the context obtained from :math:`Γ_P` by replacing each :math:`P_l` that is
      an arity with :math:`P_l'` for :math:`1≤ l ≤ r` (notice that :math:`P_l` arity implies :math:`P_l'`
      arity since :math:`E[] ⊢ P_l' ≤_{βδιζη} \subst{P_l}{p_u}{q_u}_{u=1\ldots l-1}`);
    + there are sorts :math:`s_i`, for :math:`1 ≤ i ≤ k` such that, for
      :math:`Γ_{I'} = [I_1 :∀ Γ_{P'} ,(A_1)_{/s_1} ;~…;~I_k :∀ Γ_{P'} ,(A_k)_{/s_k}]`
      we have :math:`(E[Γ_{I′} ;Γ_{P′}] ⊢ C_i : s_{q_i})_{i=1… n}` ;
    + the sorts :math:`s_i` are all introduced by the inductive
      declaration and have no universe constraints beside being greater
      than or equal to :math:`\Prop`, and such that all
      eliminations, to :math:`\Prop`, :math:`\Set` and :math:`\Type(j)`,
      are allowed (see Section :ref:`Destructors`).


Notice that if :math:`I_j~q_1 … q_r` is typable using the rules **Ind-Const** and
**App**, then it is typable using the rule **Ind-Family**. Conversely, the
extended theory is not stronger than the theory without **Ind-Family**. We
get an equiconsistency result by mapping each :math:`\ind{p}{Γ_I}{Γ_C}`
occurring into a given derivation into as many different inductive
types and constructors as the number of different (partial)
replacements of sorts, needed for this derivation, in the parameters
that are arities (this is possible because :math:`\ind{p}{Γ_I}{Γ_C}` well-formed
implies that :math:`\ind{p}{Γ_{I'}}{Γ_{C'}}` is well-formed and has the
same allowed eliminations, where :math:`Γ_{I′}` is defined as above and
:math:`Γ_{C′} = [c_1 :∀ Γ_{P′} ,C_1 ;~…;~c_n :∀ Γ_{P′} ,C_n ]`). That is, the changes in the
types of each partial instance :math:`q_1 … q_r` can be characterized by the
ordered sets of arity sorts among the types of parameters, and to each
signature is associated a new inductive definition with fresh names.
Conversion is preserved as any (partial) instance :math:`I_j~q_1 … q_r` or
:math:`C_i~q_1 … q_r` is mapped to the names chosen in the specific instance of
:math:`\ind{p}{Γ_I}{Γ_C}`.

.. warning::

   The restriction that sorts are introduced by the inductive
   declaration prevents inductive types declared in sections to be
   template-polymorphic on universes introduced previously in the
   section: they cannot parameterize over the universes introduced with
   section variables that become parameters at section closing time, as
   these may be shared with other definitions from the same section
   which can impose constraints on them.

.. flag:: Auto Template Polymorphism

   This :term:`flag`, enabled by default, makes every inductive type declared
   at level :math:`\Type` (without an explicit universe instance or hiding it behind a
   definition) template polymorphic if possible.

   This can be prevented using the :attr:`universes(template=no) <universes(template)>`
   attribute.

   Template polymorphism and full universe polymorphism (see Chapter
   :ref:`polymorphicuniverses`) are incompatible, so if the latter is
   enabled (through the :flag:`Universe Polymorphism` flag or the
   :attr:`universes(polymorphic)` attribute) it will prevail over
   automatic template polymorphism.

.. warn:: Automatically declaring @ident as template polymorphic.

   Warning ``auto-template`` can be used (it is off by default) to
   find which types are implicitly declared template polymorphic by
   :flag:`Auto Template Polymorphism`.

   An inductive type can be forced to be template polymorphic using
   the :attr:`universes(template)` attribute: in this case, the
   warning is not emitted.

.. attr:: universes(template{? = {| yes | no } })
   :name: universes(template)

   This :term:`boolean attribute` can be used to explicitly declare an
   inductive type as template polymorphic, whether the :flag:`Auto
   Template Polymorphism` flag is on or off.

   .. exn:: template and polymorphism not compatible

      This attribute cannot be used in a full universe polymorphic
      context, i.e. if the :flag:`Universe Polymorphism` flag is on or
      if the :attr:`universes(polymorphic)` attribute is used.

   .. exn:: Ill-formed template inductive declaration: not polymorphic on any universe.

      The attribute was used but the inductive definition does not
      satisfy the criterion to be template polymorphic.

   When ``universes(template=no)`` is used, it will prevent an
   inductive type to be template polymorphic, even if the :flag:`Auto
   Template Polymorphism` flag is on.

In practice, the rule **Ind-Family** is used by Rocq only when there is only one
inductive type in the inductive definition and it is declared with an arity
whose sort is in the Type hierarchy. Then, the polymorphism is over
the parameters whose type is an arity of sort in the Type hierarchy.
The sorts :math:`s_j` are chosen canonically so that each :math:`s_j` is minimal with
respect to the hierarchy :math:`\Prop ⊂ \Set_p ⊂ \Type` where :math:`\Set_p` is predicative
:math:`\Set`. More precisely, an empty or small singleton inductive definition
(i.e. an inductive definition of which all inductive types are
singleton – see Section :ref:`Destructors`) is set in :math:`\Prop`, a small non-singleton
inductive type is set in :math:`\Set` (even in case :math:`\Set` is impredicative – see
:ref:`The-Calculus-of-Inductive-Construction-with-impredicative-Set`),
and otherwise in the Type hierarchy.

Note that the side-condition about allowed elimination sorts in the rule
**Ind-Family** avoids to recompute the allowed elimination sorts at each
instance of a pattern matching (see Section :ref:`Destructors`). As an
example, let us consider the following definition:

.. example::

   .. rocqtop:: in

      Inductive option (A:Type) : Type :=
      | None : option A
      | Some : A -> option A.

As the definition is set in the Type hierarchy, it is used
polymorphically over its parameters whose types are arities of a sort
in the Type hierarchy. Here, the parameter :math:`A` has this property, hence,
if :g:`option` is applied to a type in :math:`\Set`, the result is in :math:`\Set`. Note that
if :g:`option` is applied to a type in :math:`\Prop`, then, the result is not set in
:math:`\Prop` but in :math:`\Set` still. This is because :g:`option` is not a singleton type
(see Section :ref:`Destructors`) and it would lose the elimination to :math:`\Set` and :math:`\Type`
if set in :math:`\Prop`.

.. example::

   .. rocqtop:: all

      Check (fun A:Set => option A).
      Check (fun A:Prop => option A).

Here is another example.

.. example::

   .. rocqtop:: in

      Inductive prod (A B:Type) : Type := pair : A -> B -> prod A B.

As :g:`prod` is a singleton type, it will be in :math:`\Prop` if applied twice to
propositions, in :math:`\Set` if applied twice to at least one type in :math:`\Set` and
none in :math:`\Type`, and in :math:`\Type` otherwise. In all cases, the three kind of
eliminations schemes are allowed.

.. example::

   .. rocqtop:: all

      Check (fun A:Set => prod A).
      Check (fun A:Prop => prod A A).
      Check (fun (A:Prop) (B:Set) => prod A B).
      Check (fun (A:Type) (B:Prop) => prod A B).

.. note::
   Template polymorphism used to be called “sort-polymorphism of
   inductive types” before universe polymorphism
   (see Chapter :ref:`polymorphicuniverses`) was introduced.


.. _Destructors:

Destructors
~~~~~~~~~~~~~~~~~

The specification of inductive definitions with arities and
constructors is quite natural. But we still have to say how to use an
object in an inductive type.

This problem is rather delicate. There are actually several different
ways to do that. Some of them are logically equivalent but not always
equivalent from the computational point of view or from the user point
of view.

From the computational point of view, we want to be able to define a
function whose domain is an inductively defined type by using a
combination of case analysis over the possible constructors of the
object and recursion.

Because we need to keep a consistent theory and also we prefer to keep
a strongly normalizing reduction, we cannot accept any sort of
recursion (even terminating). So the basic idea is to restrict
ourselves to primitive recursive functions and functionals.

For instance, assuming a parameter :math:`A:\Set` exists in the local context,
we want to build a function :math:`\length` of type :math:`\List~A → \nat` which computes
the length of the list, such that :math:`(\length~(\Nil~A)) = \nO` and
:math:`(\length~(\cons~A~a~l)) = (\nS~(\length~l))`.
We want these equalities to be
recognized implicitly and taken into account in the conversion rule.

From the logical point of view, we have built a type family by giving
a set of constructors. We want to capture the fact that we do not have
any other way to build an object in this type. So when trying to prove
a property about an object :math:`m` in an inductive type it is enough
to enumerate all the cases where :math:`m` starts with a different
constructor.

In case the inductive definition is effectively a recursive one, we
want to capture the extra property that we have built the smallest
fixed point of this recursive equation. This says that we are only
manipulating finite objects. This analysis provides induction
principles. For instance, in order to prove
:math:`∀ l:\List~A,~(\kw{has}\_\kw{length}~A~l~(\length~l))` it is enough to prove:


+ :math:`(\kw{has}\_\kw{length}~A~(\Nil~A)~(\length~(\Nil~A)))`
+ :math:`∀ a:A,~∀ l:\List~A,~(\kw{has}\_\kw{length}~A~l~(\length~l)) →`
  :math:`(\kw{has}\_\kw{length}~A~(\cons~A~a~l)~(\length~(\cons~A~a~l)))`


which given the conversion equalities satisfied by :math:`\length` is the same
as proving:


+ :math:`(\kw{has}\_\kw{length}~A~(\Nil~A)~\nO)`
+ :math:`∀ a:A,~∀ l:\List~A,~(\kw{has}\_\kw{length}~A~l~(\length~l)) →`
  :math:`(\kw{has}\_\kw{length}~A~(\cons~A~a~l)~(\nS~(\length~l)))`


One conceptually simple way to do that, following the basic scheme
proposed by Martin-Löf in his Intuitionistic Type Theory, is to
introduce for each inductive definition an elimination operator. At
the logical level it is a proof of the usual induction principle and
at the computational level it implements a generic operator for doing
primitive recursion over the structure.

But this operator is rather tedious to implement and use. We choose
to factorize the operator for primitive recursion
into two more primitive operations as was first suggested by Th.
Coquand in :cite:`Coq92`. One is the definition by pattern matching. The
second one is a definition by guarded fixpoints.


.. _match-construction:

The match ... with ... end construction
+++++++++++++++++++++++++++++++++++++++

The basic idea of this operator is that we have an object :math:`m` in an
inductive type :math:`I` and we want to prove a property which possibly
depends on :math:`m`. For this, it is enough to prove the property for
:math:`m = (c_i~u_1 … u_{p_i} )` for each constructor of :math:`I`.
The Rocq term for this proof
will be written:

.. math::
   \Match~m~\with~(c_1~x_{11} ... x_{1p_1} ) ⇒ f_1 | … | (c_n~x_{n1} ... x_{np_n} ) ⇒ f_n~\kwend

In this expression, if :math:`m` eventually happens to evaluate to
:math:`(c_i~u_1 … u_{p_i})` then the expression will behave as specified in its :math:`i`-th branch
and it will reduce to :math:`f_i` where the :math:`x_{i1} …x_{ip_i}` are replaced by the
:math:`u_1 … u_{p_i}` according to the ι-reduction.

Actually, for type checking a :math:`\Match…\with…\kwend` expression we also need
to know the predicate :math:`P` to be proved by case analysis. In the general
case where :math:`I` is an inductively defined :math:`n`-ary relation, :math:`P` is a predicate
over :math:`n+1` arguments: the :math:`n` first ones correspond to the arguments of :math:`I`
(parameters excluded), and the last one corresponds to object :math:`m`. Rocq
can sometimes infer this predicate but sometimes not. The concrete
syntax for describing this predicate uses the :math:`\as…\In…\return`
construction. For instance, let us assume that :math:`I` is an unary predicate
with one parameter and one argument. The predicate is made explicit
using the syntax:

.. math::
   \Match~m~\as~x~\In~I~\_~a~\return~P~\with~
   (c_1~x_{11} ... x_{1p_1} ) ⇒ f_1 | …
   | (c_n~x_{n1} ... x_{np_n} ) ⇒ f_n~\kwend

The :math:`\as` part can be omitted if either the result type does not depend
on :math:`m` (non-dependent elimination) or :math:`m` is a variable (in this case, :math:`m`
can occur in :math:`P` where it is considered a bound variable). The :math:`\In` part
can be omitted if the result type does not depend on the arguments
of :math:`I`. Note that the arguments of :math:`I` corresponding to parameters *must*
be :math:`\_`, because the result type is not generalized to all possible
values of the parameters. The other arguments of :math:`I` (sometimes called
indices in the literature) have to be variables (:math:`a` above) and these
variables can occur in :math:`P`. The expression after :math:`\In` must be seen as an
*inductive type pattern*. Notice that expansion of implicit arguments
and notations apply to this pattern. For the purpose of presenting the
inference rules, we use a more compact notation:

.. math::
   \case(m,(λ a x . P), λ x_{11} ... x_{1p_1} . f_1~| … |~λ x_{n1} ...x_{np_n} . f_n )


.. _Allowed-elimination-sorts:

**Allowed elimination sorts.** An important question for building the typing rule for :math:`\Match` is what
can be the type of :math:`λ a x . P` with respect to the type of :math:`m`. If :math:`m:I`
and :math:`I:A` and :math:`λ a x . P : B` then by :math:`[I:A|B]` we mean that one can use
:math:`λ a x . P` with :math:`m` in the above match-construct.


.. _cic_notations:

**Notations.** The :math:`[I:A|B]` is defined as the smallest relation satisfying the
following rules: We write :math:`[I|B]` for :math:`[I:A|B]` where :math:`A` is the type of :math:`I`.

The case of inductive types in sorts :math:`\Set` or :math:`\Type` is simple.
There is no restriction on the sort of the predicate to be eliminated.

.. inference:: Prod

   [(I~x):A′|B′]
   -----------------------
   [I:∀ x:A,~A′|∀ x:A,~B′]


.. inference:: Set & Type

   s_1 ∈ \{\Set,\Type(j)\}
   s_2 ∈ \Sort
   ----------------
   [I:s_1 |I→ s_2 ]


The case of Inductive definitions of sort :math:`\Prop` is a bit more
complicated, because of our interpretation of this sort. The only
harmless allowed eliminations, are the ones when predicate :math:`P`
is also of sort :math:`\Prop` or is of the morally smaller sort
:math:`\SProp`.

.. inference:: Prop

   s ∈ \{\SProp,\Prop\}
   --------------------
   [I:\Prop|I→s]


:math:`\Prop` is the type of logical propositions, the proofs of properties :math:`P` in
:math:`\Prop` could not be used for computation and are consequently ignored by
the extraction mechanism. Assume :math:`A` and :math:`B` are two propositions, and the
logical disjunction :math:`A ∨ B` is defined inductively by:

.. example::

   .. rocqtop:: in

      Inductive or (A B:Prop) : Prop :=
      or_introl : A -> or A B | or_intror : B -> or A B.


The following definition which computes a boolean value by case over
the proof of :g:`or A B` is not accepted:

.. example::

   .. rocqtop:: all

      Fail Definition choice (A B: Prop) (x:or A B) :=
      match x with or_introl _ _ a => true | or_intror _ _ b => false end.

From the computational point of view, the structure of the proof of
:g:`(or A B)` in this term is needed for computing the boolean value.

In general, if :math:`I` has type :math:`\Prop` then :math:`P` cannot have type :math:`I→\Set`, because
it will mean to build an informative proof of type :math:`(P~m)` doing a case
analysis over a non-computational object that will disappear in the
extracted program. But the other way is safe with respect to our
interpretation we can have :math:`I` a computational object and :math:`P` a
non-computational one, it just corresponds to proving a logical property
of a computational object.

In the same spirit, elimination on :math:`P` of type :math:`I→\Type` cannot be allowed
because it trivially implies the elimination on :math:`P` of type :math:`I→ \Set` by
cumulativity. It also implies that there are two proofs of the same
property which are provably different, contradicting the
proof-irrelevance property which is sometimes a useful axiom:

.. example::

   .. rocqtop:: all

      Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.

The elimination of an inductive type of sort :math:`\Prop` on a predicate
:math:`P` of type :math:`I→ \Type` leads to a paradox when applied to impredicative
inductive definition like the second-order existential quantifier
:g:`exProp` defined above, because it gives access to the two projections on
this type.


.. _Empty-and-singleton-elimination:

**Empty and singleton elimination.** There are special inductive definitions in
:math:`\Prop` for which more eliminations are allowed.

.. inference:: Prop-extended

   I~\kw{is an empty or singleton definition}
   s ∈ \Sort
   -------------------------------------
   [I:\Prop|I→ s]

A *singleton definition* has only one constructor and all the
arguments of this constructor have type :math:`\Prop`. In that case, there is a
canonical way to interpret the informative extraction on an object in
that type, such that the elimination on any sort :math:`s` is legal. Typical
examples are the conjunction of non-informative propositions and the
equality. If there is a hypothesis :math:`h:a=b` in the local context, it can
be used for rewriting not only in logical propositions but also in any
type.

.. example::

   .. rocqtop:: all

      Print eq_rec.
      Require Extraction.
      Extraction eq_rec.

An empty definition has no constructors, in that case also,
elimination on any sort is allowed.

.. _Eliminaton-for-SProp:

Inductive types in :math:`\SProp` must have no constructors (i.e. be
empty) to be eliminated to produce relevant values.

Note that thanks to proof irrelevance elimination functions can be
produced for other types, for instance the elimination for a unit type
is the identity.

.. _Type-of-branches:

**Type of branches.**
Let :math:`c` be a term of type :math:`C`, we assume :math:`C` is a type of constructor for an
inductive type :math:`I`. Let :math:`P` be a term that represents the property to be
proved. We assume :math:`r` is the number of parameters and :math:`s` is the number of
arguments.

We define a new type :math:`\{c:C\}^P` which represents the type of the branch
corresponding to the :math:`c:C` constructor.

.. math::
   \begin{array}{ll}
   \{c:(I~q_1\ldots q_r\ t_1 \ldots t_s)\}^P &\equiv (P~t_1\ldots ~t_s~c) \\
   \{c:∀ x:T,~C\}^P &\equiv ∀ x:T,~\{(c~x):C\}^P
   \end{array}

We write :math:`\{c\}^P` for :math:`\{c:C\}^P` with :math:`C` the type of :math:`c`.


.. example::

   The following term in concrete syntax::

       match t as l return P' with
       | nil _ => t1
       | cons _ hd tl => t2
       end


   can be represented in abstract syntax as

   .. math::
      \case(t,P,f_1 | f_2 )

   where

   .. math::
      :nowrap:

      \begin{eqnarray*}
        P & = & λ l.~P^\prime\\
        f_1 & = & t_1\\
        f_2 & = & λ (hd:\nat).~λ (tl:\List~\nat).~t_2
      \end{eqnarray*}

   According to the definition:

   .. math::
      \{(\Nil~\nat)\}^P ≡ \{(\Nil~\nat) : (\List~\nat)\}^P ≡ (P~(\Nil~\nat))

   .. math::

      \begin{array}{rl}
      \{(\cons~\nat)\}^P & ≡\{(\cons~\nat) : (\nat→\List~\nat→\List~\nat)\}^P \\
      & ≡∀ n:\nat,~\{(\cons~\nat~n) : (\List~\nat→\List~\nat)\}^P \\
      & ≡∀ n:\nat,~∀ l:\List~\nat,~\{(\cons~\nat~n~l) : (\List~\nat)\}^P \\
      & ≡∀ n:\nat,~∀ l:\List~\nat,~(P~(\cons~\nat~n~l)).
      \end{array}

   Given some :math:`P` then :math:`\{(\Nil~\nat)\}^P` represents the expected type of :math:`f_1`,
   and :math:`\{(\cons~\nat)\}^P` represents the expected type of :math:`f_2`.


.. _Typing-rule:

**Typing rule.**
Our very general destructor for inductive definitions has the
following typing rule

.. inference:: match

   \begin{array}{l}
   E[Γ] ⊢ c : (I~q_1 … q_r~t_1 … t_s ) \\
   E[Γ] ⊢ P : B \\
   [(I~q_1 … q_r)|B] \\
   (E[Γ] ⊢ f_i : \{(c_{p_i}~q_1 … q_r)\}^P)_{i=1… l}
   \end{array}
   ------------------------------------------------
   E[Γ] ⊢ \case(c,P,f_1  |… |f_l ) : (P~t_1 … t_s~c)

provided :math:`I` is an inductive type in a
definition :math:`\ind{r}{Γ_I}{Γ_C}` with :math:`Γ_C = [c_1 :C_1 ;~…;~c_n :C_n ]` and
:math:`c_{p_1} … c_{p_l}` are the only constructors of :math:`I`.



.. example::

   Below is a typing rule for the term shown in the previous example:

   .. inference:: list example

     \begin{array}{l}
       E[Γ] ⊢ t : (\List ~\nat) \\
       E[Γ] ⊢ P : B \\
       [(\List ~\nat)|B] \\
       E[Γ] ⊢ f_1 : \{(\Nil ~\nat)\}^P \\
       E[Γ] ⊢ f_2 : \{(\cons ~\nat)\}^P
     \end{array}
     ------------------------------------------------
     E[Γ] ⊢ \case(t,P,f_1 |f_2 ) : (P~t)


.. _Definition-of-ι-reduction:

**Definition of ι-reduction.**
We still have to define the ι-reduction in the general case.

An ι-redex is a term of the following form:

.. math::
   \case((c_{p_i}~q_1 … q_r~a_1 … a_m ),P,f_1 |… |f_l )

with :math:`c_{p_i}` the :math:`i`-th constructor of the inductive type :math:`I` with :math:`r`
parameters.

The ι-contraction of this term is :math:`(f_i~a_1 … a_m )` leading to the
general reduction rule:

.. math::
   \case((c_{p_i}~q_1 … q_r~a_1 … a_m ),P,f_1 |… |f_l ) \triangleright_ι (f_i~a_1 … a_m )


.. _Fixpoint-definitions:

Fixpoint definitions
~~~~~~~~~~~~~~~~~~~~

The second operator for elimination is fixpoint definition. This
fixpoint may involve several mutually recursive definitions. The basic
concrete syntax for a recursive set of mutually recursive declarations
is (with :math:`Γ_i` contexts):

.. math::
   \fix~f_1 (Γ_1 ) :A_1 :=t_1~\with … \with~f_n (Γ_n ) :A_n :=t_n


The terms are obtained by projections from this set of declarations
and are written

.. math::
   \fix~f_1 (Γ_1 ) :A_1 :=t_1~\with … \with~f_n (Γ_n ) :A_n :=t_n~\for~f_i

In the inference rules, we represent such a term by

.. math::
   \Fix~f_i\{f_1 :A_1':=t_1' … f_n :A_n':=t_n'\}

with :math:`t_i'` (resp. :math:`A_i'`) representing the term :math:`t_i` abstracted (resp.
generalized) with respect to the bindings in the context :math:`Γ_i`, namely
:math:`t_i'=λ Γ_i . t_i` and :math:`A_i'=∀ Γ_i , A_i`.


Typing rule
+++++++++++

The typing rule is the expected one for a fixpoint.

.. inference:: Fix

   (E[Γ] ⊢ A_i : s_i )_{i=1… n}
   (E[Γ;~f_1 :A_1 ;~…;~f_n :A_n ] ⊢ t_i : A_i )_{i=1… n}
   -------------------------------------------------------
   E[Γ] ⊢ \Fix~f_i\{f_1 :A_1 :=t_1 … f_n :A_n :=t_n \} : A_i


Any fixpoint definition cannot be accepted because non-normalizing
terms allow proofs of absurdity. The basic scheme of recursion that
should be allowed is the one needed for defining primitive recursive
functionals. In that case the fixpoint enjoys a special syntactic
restriction, namely one of the arguments belongs to an inductive type,
the function starts with a case analysis and recursive calls are done
on variables coming from patterns and representing subterms. For
instance in the case of natural numbers, a proof of the induction
principle of type

.. math::
   ∀ P:\nat→\Prop,~(P~\nO)→(∀ n:\nat,~(P~n)→(P~(\nS~n)))→ ∀ n:\nat,~(P~n)

can be represented by the term:

.. math::
   \begin{array}{l}
   λ P:\nat→\Prop.~λ f:(P~\nO).~λ g:(∀ n:\nat,~(P~n)→(P~(\nS~n))).\\
   \Fix~h\{h:∀ n:\nat,~(P~n):=λ n:\nat.~\case(n,P,f | λp:\nat.~(g~p~(h~p)))\}
   \end{array}

Before accepting a fixpoint definition as being correctly typed, we
check that the definition is “guarded”. A precise analysis of this
notion can be found in :cite:`Gim94`. The first stage is to precise on which
argument the fixpoint will be decreasing. The type of this argument
should be an inductive type. For doing this, the syntax of
fixpoints is extended and becomes

.. math::
   \Fix~f_i\{f_1/k_1 :A_1:=t_1 … f_n/k_n :A_n:=t_n\}


where :math:`k_i` are positive integers. Each :math:`k_i` represents the index of
parameter of :math:`f_i`, on which :math:`f_i` is decreasing. Each :math:`A_i` should be a
type (reducible to a term) starting with at least :math:`k_i` products
:math:`∀ y_1 :B_1 ,~… ∀ y_{k_i} :B_{k_i} ,~A_i'` and :math:`B_{k_i}` an inductive type.

Now in the definition :math:`t_i`, if :math:`f_j` occurs then it should be applied to
at least :math:`k_j` arguments and the :math:`k_j`-th argument should be
syntactically recognized as structurally smaller than :math:`y_{k_i}`.

The definition of being structurally smaller is a bit technical. One
needs first to define the notion of *recursive arguments of a
constructor*. For an inductive definition :math:`\ind{r}{Γ_I}{Γ_C}`, if the
type of a constructor :math:`c` has the form
:math:`∀ p_1 :P_1 ,~… ∀ p_r :P_r,~∀ x_1:T_1,~… ∀ x_m :T_m,~(I_j~p_1 … p_r~t_1 … t_s )`,
then the recursive
arguments will correspond to :math:`T_i` in which one of the :math:`I_l` occurs.

The main rules for being structurally smaller are the following.
Given a variable :math:`y` of an inductively defined type in a declaration
:math:`\ind{r}{Γ_I}{Γ_C}` where :math:`Γ_I` is :math:`[I_1 :A_1 ;~…;~I_k :A_k]`, and :math:`Γ_C` is
:math:`[c_1 :C_1 ;~…;~c_n :C_n ]`, the terms structurally smaller than :math:`y` are:


+ :math:`(t~u)` and :math:`λ x:U .~t` when :math:`t` is structurally smaller than :math:`y`.
+ :math:`\case(c,P,f_1 … f_n)` when each :math:`f_i` is structurally smaller than :math:`y`.
  If :math:`c` is :math:`y` or is structurally smaller than :math:`y`, its type is an inductive
  type :math:`I_p` part of the inductive definition corresponding to :math:`y`.
  Each :math:`f_i` corresponds to a type of constructor
  :math:`C_q ≡ ∀ p_1 :P_1 ,~…,∀ p_r :P_r ,~∀ y_1 :B_1 ,~… ∀ y_m :B_m ,~(I_p~p_1 … p_r~t_1 … t_s )`
  and can consequently be written :math:`λ y_1 :B_1' .~… λ y_m :B_m'.~g_i`. (:math:`B_i'` is
  obtained from :math:`B_i` by substituting parameters for variables) the variables
  :math:`y_j` occurring in :math:`g_i` corresponding to recursive arguments :math:`B_i` (the
  ones in which one of the :math:`I_l` occurs) are structurally smaller than :math:`y`.


The following definitions are correct, we enter them using the :cmd:`Fixpoint`
command and show the internal representation.

.. example::

   .. rocqtop:: all

      Fixpoint plus (n m:nat) {struct n} : nat :=
      match n with
      | O => m
      | S p => S (plus p m)
      end.

      Print plus.
      Fixpoint lgth (A:Set) (l:list A) {struct l} : nat :=
      match l with
      | nil _ => O
      | cons _ a l' => S (lgth A l')
      end.
      Print lgth.
      Fixpoint sizet (t:tree) : nat := let (f) := t in S (sizef f)
      with sizef (f:forest) : nat :=
      match f with
      | emptyf => O
      | consf t f => plus (sizet t) (sizef f)
      end.
      Print sizet.

.. _Reduction-rule:

Reduction rule
++++++++++++++

Let :math:`F` be the set of declarations:
:math:`f_1 /k_1 :A_1 :=t_1 …f_n /k_n :A_n:=t_n`.
The reduction for fixpoints is:

.. math::
   (\Fix~f_i \{F\}~a_1 …a_{k_i}) ~\triangleright_ι~ \subst{t_i}{f_k}{\Fix~f_k \{F\}}_{k=1… n} ~a_1 … a_{k_i}

when :math:`a_{k_i}` starts with a constructor. This last restriction is needed
in order to keep strong normalization and corresponds to the reduction
for primitive recursive operators. The following reductions are now
possible:

.. math::
   :nowrap:

   \begin{eqnarray*}
   \plus~(\nS~(\nS~\nO))~(\nS~\nO)~& \trii & \nS~(\plus~(\nS~\nO)~(\nS~\nO))\\
                                   & \trii & \nS~(\nS~(\plus~\nO~(\nS~\nO)))\\
                                   & \trii & \nS~(\nS~(\nS~\nO))\\
   \end{eqnarray*}

.. _Mutual-induction:

**Mutual induction**

The principles of mutual induction can be automatically generated
using the Scheme command described in Section :ref:`proofschemes-induction-principles`.
