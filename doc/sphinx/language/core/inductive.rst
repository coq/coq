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
