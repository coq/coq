.. _inductive:

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
      inductive_definition ::= @ident {? @cumul_univ_decl } {* @binder } {? %| {* @binder } } {? : @type } := {? {? %| } {+| @constructor } } {? @decl_notations }
      constructor ::= {* #[ {+, @attribute } ] } @ident {* @binder } {? of {+& @term99 } } {? @of_type_inst }

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

   This commands supports :attr:`schemes` to control the automatic
   generation of inductive principles.

   .. flag:: Dependent Proposition Eliminators

      The inductive principles express dependent elimination when the
      inductive type allows it (always true when not using
      :flag:`Primitive Projections`), except by default when the
      inductive is explicitly declared in `Prop`.

      The dependent elimination corresponds to the "Induction"
      :n:`@scheme_type`, and non-dependent elimination to
      "Minimality".

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

   :n:`{? of {+& @term99 } }`
     `of T1 & ... & Tn` is syntactic sugar for anonymous binders `(_ : T1) ... (_ : Tn)`.

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

Writing Recursive Functions using Fixpoints
-------------------------------------------

Rocq provides primitive support for defining recursive functions over
inductive types using fixpoints. The recommended way to declare such functions
is the top-level :cmd:`Fixpoint` command. Recursive functions can also be
written directly within a term using a :n:`fix` expression, which is the
construction to which :cmd:`Fixpoint` declarations are elaborated.

The following subsections describe these two forms and their use.
Rocq only accepts terminating recursive functions to preserve consistency.
Termination checking is performed by the :ref:`guard condition <guard-condition>`.

.. _Fixpoint:

Top-level recursive functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The :cmd:`Fixpoint` command declares functions defined by structural recursion
over inductive types.

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

   This command accepts the following attributes:

   + For locality and section variables: :attr:`local`, :attr:`global`, and :attr:`using`
   + For universes: :attr:`universes(polymorphic)`,
     :attr:`universes(collapse_sort_variables)`, :attr:`bypass_check(universes)`
   + For using advanced proof mode / elaboration: :attr:`refine`, :attr:`program`
   + To disable guard checking: :attr:`bypass_check(guard)`
   + For documentation: :attr:`deprecated`, :attr:`warn`

   :cmd:`Fixpoint` without the :attr:`program` attribute does not support the
   :n:`wf` or :n:`measure` clauses of :n:`@fixannot`. See :ref:`program_fixpoint`.

   The :n:`{struct @ident}` annotation (see :n:`@fixannot`) selects the
   *structural argument*, also called the decreasing argument. Definitions
   must satisfy the :ref:`guard condition <guard-condition>` for that
   argument. A fixpoint is unfolded only when the structural argument is
   instantiated with a term starting with a constructor.

   If the :n:`{struct @ident}` annotation is omitted, Rocq tries arguments from
   left to right until it finds one that satisfies the guard condition.
   Specifying the structural argument explicitly can therefore significantly speed up
   type checking of large mutual fixpoints.

   .. _example_minimum:

   .. example:: Minimum of two natural numbers

      The following function computes the minimum of two natural numbers.
      It matches both arguments: if both are successors, it adds one to the
      minimum of their predecessors; otherwise, it returns zero. The structural
      argument is inferred to be :g:`n`.

      .. rocqtop:: in

         Fixpoint min_left (n m : nat) : nat :=
           match n with
           | 0 => 0
           | S p =>
             match m with
             | 0 => 0
             | S q => S (min_left p q)
             end
           end.

      The function unfolds when its first argument starts with a constructor.
      For :g:`0`, it reduces to :g:`0`, even when :g:`m` is a variable:

      .. rocqtop:: in

         Goal forall m : nat, min_left 0 m = 0.
         Proof.
           reflexivity.
         Qed.

      For :g:`S p`, it reduces to the inner match on :g:`m`. This match returns
      :g:`0` when :g:`m` is :g:`0`, and :g:`S (min_left p q)` when :g:`m` is
      :g:`S q`:

      .. rocqtop:: in

         Goal forall p m : nat,
           min_left (S p) m =
             match m with
             | 0 => 0
             | S q => S (min_left p q)
             end.
         Proof.
           reflexivity.
         Qed.

   Some fixpoints satisfy the guard condition for more than one argument.
   The choice affects reduction, since a fixpoint unfolds only when its structural
   argument starts with a constructor. An explicit annotation is needed to
   select an argument other than the first one accepted by Rocq.

   .. _reversed_add_example:

   .. _alternative_struct_example:

   .. example:: Choosing another structural argument

      In :g:`min_left`, the recursive call decreases both :g:`n` and :g:`m`.
      The same body can therefore use :g:`m` as its structural argument.

      .. rocqtop:: in

         Fixpoint min_right (n m : nat) {struct m} : nat :=
           match n with
           | 0 => 0
           | S p =>
             match m with
             | 0 => 0
             | S q => S (min_right p q)
             end
           end.

      Both functions compute the same minimum, but :g:`m` now controls unfolding.
      Unlike :g:`min_left 0 m` in the :ref:`previous example <example_minimum>`,
      :g:`min_right 0 m` cannot unfold while :g:`m` is a variable.
      Its value can still be shown to be zero by case analysis on :g:`m`:

      .. rocqtop:: in

         Goal forall m : nat, min_right 0 m = 0.
         Proof.
           Fail reflexivity.
           destruct m; reflexivity.
         Qed.

      Conversely, :g:`min_right` unfolds when :g:`m` starts with a constructor,
      even when :g:`n` is a variable, whereas :g:`min_left` does not:

      .. rocqtop:: in

         Goal forall n : nat,
           min_right n 0 = match n with 0 => 0 | S _ => 0 end.
         Proof.
           reflexivity.
         Qed.

   The :n:`with` clause enables users to declare mutually recursive functions.
   In particular, it can be used to declare functions over mutually defined
   inductive types.

   .. _example_mutual_fixpoints:

   .. example:: Mutual fixpoints

      For the mutually defined types :g:`tree` and :g:`forest`, the size
      functions call each other when traversing their recursive arguments:

      .. rocqtop:: in

         Fixpoint tree_size (t:tree) : nat :=
           match t with
           | node a f => S (forest_size f)
           end
         with forest_size (f:forest) : nat :=
           match f with
           | leaf b => 1
           | cons t f' => (tree_size t + forest_size f')
           end.

   If :n:`@term` is omitted, :n:`@type` is required and Rocq enters proof mode.
   This allows the body to be constructed incrementally using tactics.
   Moreover, the :attr:`refine` attribute allows specific parts of the body to be
   constructed in proof mode by replacing them with :g:`_`.
   The definition must be closed with :cmd:`Defined` to keep the resulting
   :term:`constant` transparent and allow the function to unfold and compute.

   .. example:: Constructing a fixpoint in proof mode

      The following definition doubles a natural number. Case analysis creates
      a goal for each constructor, and :tacn:`exact` supplies the corresponding
      branch of the body. The successor branch makes a recursive call on the
      predecessor :g:`p`.

      .. rocqtop:: in

         Fixpoint double (n : nat) : nat.
         Proof.
           destruct n as [|p].
           - exact 0.
           - exact (S (S (double p))).
         Defined.

      .. rocqtop:: all

         Compute double 3.

      .. rocqtop:: in

         #[refine]
         Fixpoint double' (n : nat) : nat :=
           match n with
           | 0 => 0
           | S p => _
           end.
         Proof.
           exact (S (S (double' p))).
         Defined.

      .. rocqtop:: all

         Compute double' 3.

Primitive fix construction
~~~~~~~~~~~~~~~~~~~~~~~~~~

Rocq provides primitive fixpoints through the :n:`fix` term constructor,
to which top-level :cmd:`Fixpoint` declarations are elaborated.

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

A local definition of a single recursive function has a special syntax:
:n:`let fix @ident {* @binder } := @term in` stands for
:n:`let @ident := fix @ident {* @binder } := @term in`. The same abbreviation
is available for cofixpoints.

The :n:`fix` and :n:`let fix` expressions support only the :n:`struct` form of
:n:`@fixannot`. The :n:`wf` and :n:`measure` forms are supported by commands
such as :cmd:`Fixpoint` with the :attr:`program` attribute and :cmd:`Function`.

The :n:`{struct @ident}` annotation selects the structural argument as for
:cmd:`Fixpoint`; it can also be omitted to let Rocq infer that argument.
Local fixpoints satisfy the same :ref:`guard condition <guard-condition>`
as top-level definitions.

It is common in functional programming to use inner fixpoints to write
tail-recursive functions. However, this has disadvantages in this case.
The resulting definition can easily unfold during proof construction, exposing
the inner fixpoint and repeating it many times in the goal and, more
importantly, in the proof term.
This can drastically increase the size of the proof term and make it much
longer to type-check, as each occurrence of the fixpoint must be type-checked
and checked for termination.
Defining the helper as a separate top-level :cmd:`Fixpoint` allows it to remain
a constant when the enclosing definition is unfolded, avoiding repeated guard
checking unless the helper itself is unfolded.

.. example:: Tail-recursive list reversal with a local fixpoint

   The function :g:`rev` uses a local helper :g:`aux` to accumulate the
   reversed list. The structural argument is the remaining input list;
   the accumulator grows with each recursive call.

   .. rocqtop:: in

      Local Open Scope list_scope.

      Definition rev {T : Type} (l : list T) : list T :=
        let fix aux (p acc : list T) {struct p} : list T :=
          match p with
          | nil => acc
          | x :: p => aux p (x :: acc)
          end
        in aux l nil.

   In the following proof, :tacn:`cbn` unfolds :g:`rev` on both sides of
   the equality and performs the first recursive call, adding :g:`n + 0`
   and :g:`n` to the respective accumulators. Since the remaining list :g:`l`
   is a variable,
   :g:`aux` cannot reduce further and remains exposed in the goal:

   .. rocqtop:: all

      Goal forall n l, rev ((n + 0) :: l) = rev (n :: l).
      Proof.
        intros n l. cbn. rewrite <- plus_n_O. reflexivity.
        Show Proof.
      Qed.

   The proof term produced by :tacn:`reflexivity` contains the exposed fixpoint.
   Type-checking this term therefore type-checks :g:`aux` and checks its
   guard condition twice, even though it was already checked when :g:`rev`
   was defined.

   In contrast, if we define :g:`rev'` with a real auxiliary function,
   the fixpoint does not unfold when simplifying the goal with :tacn:`cbn`,
   thus producing a much smaller proof term and avoiding type-checking
   and checking termination of :g:`rev_acc` twice more.

   .. rocqtop:: in

      Local Open Scope list_scope.

      Fixpoint rev_acc {T : Type} (p acc : list T) {struct p} : list T :=
        match p with
        | nil => acc
        | x :: p => rev_acc p (x :: acc)
        end.

      Definition rev' {T : Type} (l : list T) : list T := rev_acc l nil.

   .. rocqtop:: all

      Goal forall n l, rev' ((n + 0) :: l) = rev' (n :: l).
      Proof.
        intros n l. cbn. rewrite <- plus_n_O. reflexivity.
        Show Proof.
      Qed.

.. extracted from CIC chapter

.. _guard-condition:

The Guard Condition
-------------------

Rocq checks termination of fixpoints using a *guard condition*: a syntactic
check triggered every time a fixpoint is type-checked. It can also be
tested earlier in proof mode using the :cmd:`Guarded` command.

The guard condition ensures that each recursive call is performed on a strict
subterm of the structural argument, and hence, that the function terminates.
Pattern-matching on the structural argument or one of its subterms introduces
variables for strictly smaller recursive constructor arguments, on which
recursive calls are allowed.

The guard condition consists of a minimal guard and several mostly independent
extensions, described below:

+ Checking fixpoints up to reduction
+ Propagating subterm information through beta-iota cuts
+ An advanced subterm analysis that traverses fixpoints and pattern-matching

Guard checking can be disabled with :flag:`Guard Checking` or the
:attr:`bypass_check(guard)` attribute. Disabling it risks breaking consistency
and subject reduction, so it should be used with caution.

.. example:: Disabling guard checking breaks consistency

   With guard checking disabled, Rocq accepts the following fixpoint even
   though its recursive call uses the unchanged argument :g:`n`.
   The function does not terminate, and its declared return type allows us
   to prove :g:`False` by applying it to :g:`0`.

   .. rocqtop:: in

      #[bypass_check(guard)]
      Fixpoint loop (n : nat) : False := loop n.

      Unset Guard Checking.

      Fixpoint loop' (n : nat) : False := loop' n.

      Goal False.
      Proof.
        exact (loop 0).
      Qed.

Re-enabling guard checking does not recheck previously accepted definitions:
:g:`loop` remains in the environment. It is therefore possible to reason about
a function whose termination is not established by the guard condition.

.. example:: Using a previously accepted definition

   .. rocqtop:: in

      Set Guard Checking.

      Goal forall n, loop n = loop n.
      Proof.
        reflexivity.
      Qed.

However, locally disabling and then re-enabling the guard condition, or one
of its features, is not stable under reduction.
Unfolding a definition exposes its body, which must satisfy the current guard
condition when the resulting term is type-checked.
A definition accepted with weaker checks may therefore be rejected after unfolding.

.. example:: Unfolding a definition accepted without guard checking

   Unfolding :g:`loop` inserts its fixpoint into the proof term. Checking the
   guard condition of this proof term rejects the fixpoint, since guard
   checking has been re-enabled.

   .. rocqtop:: all

      Goal forall n, loop n = loop n.
      Proof.
        unfold loop. reflexivity.
        Fail Guarded.
      Abort.

Disabling and re-enabling guard checking also preserves the settings of its
individual features, as illustrated in the
:ref:`example below <preserving-subterm-analysis-settings>`.

.. _minimal-guard-condition:

Minimal Guard Condition
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The minimal guard condition requires every recursive call to be performed upon
a strictly smaller subterm of the structural argument. It can be either
a term whose weak-head normal form is a variable or a primitive projection.

Smaller variables are created by pattern-matching subterms -- strict or large --
of the structural argument: in each branch the recursive arguments of the
(mutual) inductive types are considered as strictly smaller.
For instance, pattern-matching the structural argument creates strict subterms as
the structural argument is a large subterm of itself.
Matching a term that is not a subterm creates variables which are not subterms.

.. example:: An eliminator for natural numbers

   The eliminator of :g:`nat` is recursively defined by matching the structural
   argument :g:`n` as :g:`S p`, which creates the strictly smaller variable :g:`p`
   upon which recursion can be and is performed.

   .. rocqtop:: in

      Fixpoint nat_elim (P : nat -> Type) (P0 : P 0) (PS : forall n, P n -> P (S n))
        (n : nat) {struct n} : P n :=
        match n as m return P m with
        | 0 => P0
        | S p => PS p (nat_elim P P0 PS p)
        end.

Matching a strict subterm also creates a strict subterm. This allows recursion on deep subterms.

.. example:: Recursion on a deeper subterm

   The function :g:`mod2` computes the remainder modulo two by matching its
   argument twice before making a recursive call:

   .. rocqtop:: in

      Fixpoint mod2 (n : nat) : nat :=
        match n with
        | 0 => 0
        | S p =>
          match p with
          | 0 => 1
          | S q => mod2 q
          end
        end.

   The first match exposes :g:`p` as a strict subterm of :g:`n`. The second
   exposes :g:`q` as a strict subterm of :g:`p`, and hence of :g:`n`.
   The recursive call :g:`mod2 q` is therefore accepted.

Checking termination of mutual fixpoints is no more complicated.
Each fixpoint in the mutual fixpoint must be applied to a strict subterm, and
each recursive argument is a subterm regardless of which inductive type in
the mutual block it belongs to.

.. example:: Structural decrease in mutual fixpoints

   In the :ref:`mutual fixpoint example <example_mutual_fixpoints>`, matching
   :g:`t` as :g:`node a f` exposes :g:`f` as a strict subterm of :g:`t`,
   so :g:`tree_size` may call :g:`forest_size f`. Likewise, matching
   :g:`f` as :g:`cons t f'` exposes both :g:`t` and :g:`f'` as strict
   subterms of :g:`f`, allowing the calls :g:`tree_size t` and
   :g:`forest_size f'`. In each call, the smaller part is passed as the
   structural argument of the called function. The non-recursive arguments
   :g:`a` of :g:`node` and :g:`b` of :g:`leaf` do not establish a structural
   decrease.

.. example:: Recursive call on a subterm exposed by weak-head reduction

   In the following function, recursion is performed upon :g:`(fun x => x) p`
   rather than :g:`p` itself. This is allowed as recursive calls are checked after
   weak-head reduction, which reduces this expression to :g:`p` which is strictly smaller.

   .. rocqtop:: in

      Fixpoint rid (n : nat) : nat :=
        match n with
        | 0 => 0
        | S p => S (rid ((fun x => x) p))
        end.

.. _guard-checking-reduction:

Checking Fixpoints up to Reduction
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When writing a recursive function, it can be useful to give it a local name,
pass it as an argument to another function, or partially apply it within its
own body. These uses do not immediately expose a recursive call on a strict
subterm. To support them, the guard checker reduces the enclosing expressions
and checks the recursive calls exposed by reduction.

This mechanism supports beta reduction, unfolding local and global
definitions, and reducing matches, primitive projections, fixpoints, and
cofixpoints when their reduction rules apply.

It is distinct from the weak-head reduction used by subterm analysis to
recognize recursive arguments, as in the :g:`rid` example above.
The recursive argument is itself checked for guarded recursive calls before
being reduced to determine whether it is a strict subterm.

.. example:: Instantiating a recursive argument by beta reduction

   In the body of the local function :g:`fun q => beta q`, the variable :g:`q`
   is not known to be a strict subterm of :g:`n`. Applying this function to
   :g:`p` and reducing the beta redex produces :g:`beta p`, whose recursive
   argument is a strict subterm exposed by the match.

   .. rocqtop:: in

      Fixpoint beta (n : nat) : nat :=
        match n with
        | 0 => 0
        | S p => (fun q => beta q) p
        end.

.. example:: Giving a recursive function a local name

   The binding :g:`let g := alias` gives the recursive function a local name.
   Unfolding this binding replaces :g:`g p` with :g:`alias p`, so the guard
   checker can verify that the recursive call uses the strict subterm :g:`p`.

   .. rocqtop:: in

      Fixpoint alias (n : nat) : nat :=
        let g := alias in
        match n with
        | 0 => 0
        | S p => g p
        end.

.. example:: Rejecting a recursive call exposed by reduction

   As in :g:`beta`, the call on the locally bound variable :g:`q` requires
   reduction to be checked further. Here, however, the local function is
   applied to :g:`n`. Beta reduction exposes :g:`beta_same n`, whose recursive
   argument is the unchanged structural argument rather than a strict subterm.
   The definition is therefore rejected.

   .. rocqtop:: in

      Fail Fixpoint beta_same (n : nat) : nat :=
        match n with
        | 0 => 0
        | S _ => (fun q => beta_same q) n
        end.

A recursive call on an argument already known not to be a strict subterm is
rejected before reduction, even if the call would be erased by reducing an
enclosing expression. This avoids accepting calls that would cause
nontermination under call-by-value evaluation.

.. example:: Rejecting an invalid recursive call before it can be erased

   The recursive argument :g:`S n` is not a strict subterm of :g:`n`, so the
   following definition is rejected. Reducing the :g:`let` expression would
   erase the call and return :g:`0`, but call-by-value evaluation would first
   evaluate :g:`invalid (S n)`, causing an infinite sequence of recursive calls.

   .. rocqtop:: in

      Fail Fixpoint invalid (n : nat) : nat :=
        let _ := invalid (S n) in 0.

The guard checker checks the subterms of an expression. If it detects a
partially applied recursive call or a recursive call on a locally bound variable,
the guard checker attempts to reduce the redex. If reduction is possible,
it checks the reduct.
Otherwise, the need for reduction is propagated to an outer expression, whose
reduction may instantiate or erase the delayed recursive call, allowing the
fixpoint to be accepted. The definition is rejected if this requirement remains
unresolved after checking the whole body.

.. example:: Erasing a blocked inner redex by reducing an outer one

   In the following definition, the match cannot reduce because :g:`b` is a
   variable. Its :g:`false` branch contains the partially applied recursive
   function :g:`blocked b`, which requires reduction to be checked further.
   This requirement is propagated to the enclosing :g:`let` expression.
   The bound value is unused, so reducing the :g:`let` erases the match and
   leaves :g:`0`. The definition is therefore accepted.

   .. rocqtop:: in

      Fixpoint blocked (b : bool) (n : nat) : nat :=
        let _ :=
          match b with
          | true => fun _ : nat => 0
          | false => blocked b
          end
        in 0.

.. flag:: Guard Checking Option Reduction

   This flag is on by default. Unsetting it disables reduction used to
   instantiate or erase delayed recursive calls. Ordinary structural recursion
   and weak-head reduction during subterm analysis remain available. Changing
   this flag preserves the settings of the other guard-checking features;
   disabling and re-enabling :flag:`Guard Checking` also preserves its setting.

   .. example:: Disabling recursive-call reduction

      With reduction disabled, the guard checker cannot substitute :g:`p` for
      :g:`q` in the local function below. The recursive call on :g:`q` is
      therefore rejected.

      .. rocqtop:: in

         Unset Guard Checking Option Reduction.

         Fail Fixpoint beta_off (n : nat) : nat :=
           match n with
           | 0 => 0
           | S p => (fun q => beta_off q) p
           end.

         Set Guard Checking Option Reduction.

   .. warning::

      Fixpoints written in proof mode or generated by metaprogramming often
      contain local bindings and redexes that rely on this feature. Disabling
      it may therefore cause such definitions to be rejected, even when the
      recursive calls exposed by reduction use strict subterms.

   .. warning::

      Reduction is needed to generate
      :ref:`eliminators for nested inductive types <eliminators-nested-inductive-types>`
      modularly. Disabling this flag may therefore prevent their generation.

.. _traversing-subterm-analysis:

Traversing Subterm Analysis
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The guard condition features an advanced subterm analysis that traverses fixpoints
and pattern-matching to determine whether the term recursion is performed upon
is strictly smaller than the structural argument.
This analysis traverses the definitions of the terms recursion is performed
upon; it does not prove arbitrary inequalities about their sizes.

A :n:`match` is a (strict) subterm provided every branch is a (strict) subterm,
introducing the recursive arguments using the subterm specification of the
term that is matched, as for checking termination.

An application of a mutual fixpoint :n:`fix` is a (strict) subterm provided
the fixpoint that is focussed returns an inductive type and its body is a (strict) subterm.
The body of the focussed fixpoint is analyzed using the subterm specification of
the instantiation of the structural argument, and with recursive calls to the
focussed fixpoint treated as strict subterms.
Calls to the other fixpoints in the mutual block are not considered subterms.

.. _computed-subterm-example:

.. example:: Recursive call on a computed subterm

   In the following function, recursion is performed upon :g:`m - k`, which
   does not reduce to a variable while :g:`m` is a variable.

   .. rocqtop:: in

      Fixpoint foo n k {struct n} : nat :=
        match n with
        | 0 => 0
        | S m => foo (m - k) k
        end.

   This function is accepted thanks to traversing subterm analysis, which
   unfolds :g:`Nat.sub` and traverses its definition to establish that
   :g:`m - k` is strictly smaller than the structural argument :g:`n`.

   .. rocqtop:: all

      Print Nat.sub.

   Subtraction :g:`m - k` returns :g:`m` unchanged when :g:`m` or :g:`k`
   is zero. Otherwise, recursion is performed upon the predecessor of :g:`m`.
   Since :g:`m` is already a strict subterm of :g:`n`, the unchanged result
   is strictly smaller than :g:`n`. The recursive result is also recognized
   as strictly smaller. All branches of the :n:`match` are strictly smaller;
   hence, so are the :n:`match`, the result of the fixpoint, and :g:`m - k`.

However, constructors cannot be subterms. This restriction is tied to the
reduction rule for fixpoints, which unfolds them whenever their structural
argument starts with a constructor. Allowing recursive calls on reconstructed
constructors could produce infinitely many unfoldings even on open terms,
breaking strong normalization.

.. example:: Constructors are not Subterms

   Rebuilding a term with constructors does not preserve its subterm
   information. The following identity function returns :g:`0` or :g:`S p`
   instead of the variable :g:`n` being matched:

   .. rocqtop:: in

      Definition id (n : nat) :=
       match n with
       | 0 => 0
       | S p => S p
       end.

   Although :g:`id n` is propositionally equal to :g:`n`, it is not equal to it
   by definition, and the subterm analysis cannot recognize it as a subterm.
   Matching its result therefore does not introduce a variable known to be
   smaller than the structural argument, and the following recursive call is
   rejected because :g:`id n` is not recognized as a subterm of :g:`n`:

   .. rocqtop:: all

      Fail Fixpoint zero (n : nat) : nat :=
        match (id n) with
        | 0 => 0
        | S n => zero n
        end.

   Returning the variable :g:`n` in both branches preserves its subterm
   information, as in :g:`Nat.sub` in the
   :ref:`computed-subterm example <computed-subterm-example>` above.
   The analysis can then recognize :g:`id' n` as a subterm of :g:`n`.
   In the successor branch of the outer match, recursion is performed upon
   the strictly smaller variable introduced by that match:

   .. rocqtop:: in

      Definition id' (n : nat) :=
       match n with
       | 0 => n
       | S p => n
       end.

      Fixpoint zero (n : nat) : nat :=
        match (id' n) with
        | 0 => 0
        | S n => zero n
        end.

.. flag:: Guard Checking Option Traversing Subterm Analysis

   This flag is on by default. Unsetting it disables the subterm analysis
   traversing fixpoints and pattern-matching. Recursive arguments are still
   reduced to weak-head normal form, but their heads must then be variables or
   primitive projections, as described in the
   :ref:`minimal guard condition <minimal-guard-condition>`.

   .. example:: Disabling traversing subterm analysis

      With this flag disabled, the subtraction in :g:`m - k` cannot be analyzed
      through its fixpoint. Its weak-head normal form is a fixpoint application
      blocked on the variable :g:`m`, so the following variant of :g:`foo` is
      rejected:

      .. rocqtop:: all

         Unset Guard Checking Option Traversing Subterm Analysis.

         Fail Fixpoint foo' n k {struct n} : nat :=
         match n with
         | 0 => 0
         | S m => foo' (m - k) k
         end.

   Disabling and re-enabling guard checking preserves the settings of its
   individual features.

   .. _preserving-subterm-analysis-settings:

   .. example:: Preserving subterm-analysis settings when disabling guard checking

      Traversing subterm analysis remains disabled after guard checking is
      disabled and re-enabled. Since recursion is performed upon :g:`m - k`,
      the following definition is still rejected:

      .. rocqtop:: in

         Unset Guard Checking.
         Set Guard Checking.

         Fail Fixpoint foo' n k {struct n} : nat :=
           match n with
           | 0 => 0
           | S m => foo' (m - k) k
           end.

   .. warning::

      Existing definitions, such as :g:`Fix_F` used in some support for defining
      functions by well-founded recursion, may rely on traversing subterm analysis.
      Disabling the subterm analysis can therefore cause definitions or proof terms
      obtained by unfolding such constants to be rejected, even if the constants
      were originally accepted with the flag enabled.

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

Additionally, for :math:`j=1… k` the following universe constraints must be satisfied,
or :math:`s_j` must be an impredicative sort (`SProp`, `Prop`, or if `-impredicative-set` was used `Set`)
and the `j`\th inductive may not be eliminated to larger sorts:

- for each (non parameter) constructor argument, the universe of its type must be smaller than :math:`s_j`
- if ``-indices-matter`` or :flag:`Indices Matter` was used, for each index the universe of its type must be smaller than :math:`s_j`.
  When neither ``-indices-matter`` nor :flag:`Indices Matter` is used, inductives whose indices would contribute
  universe constraints are printed by :cmd:`Print Assumptions`.
- if there are 2 or more constructors, `Set` must be smaller than :math:`s_j`
- unless the inductive is a primitive record, and unless :flag:`Definitional UIP` was used,
  if there is 1 constructor, `Prop` must be smaller than :math:`s_j` (essentially this means :math:`s_j` must not be `SProp`)

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

when the structural argument :math:`a_{k_i}` starts with a constructor.
This last restriction is needed in order to keep strong normalization
and corresponds to the reduction for primitive recursive operators.
The following reductions are now possible:

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
