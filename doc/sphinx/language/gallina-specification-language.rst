.. index::
   single: cofix

Co-recursive functions: cofix
-----------------------------

.. insertprodn term_cofix cofix_body

.. prodn::
   term_cofix ::= let cofix @cofix_body in @term
   | cofix @cofix_body {? {+ with @cofix_body } for @ident }
   cofix_body ::= @ident {* @binder } {? : @type } := @term

The expression
":n:`cofix @ident__1 @binder__1 : @type__1 with … with @ident__n @binder__n : @type__n for @ident__i`"
denotes the :math:`i`-th component of a block of terms defined by a mutual guarded
co-recursion. It is the local counterpart of the :cmd:`CoFixpoint` command. When
:math:`n=1`, the ":n:`for @ident__i`" clause is omitted.

.. _cofixpoint:

Top-level definitions of co-recursive functions
-----------------------------------------------

.. cmd:: CoFixpoint @cofix_definition {* with @cofix_definition }

   .. insertprodn cofix_definition cofix_definition

   .. prodn::
      cofix_definition ::= @ident_decl {* @binder } {? : @type } {? := @term } {? @decl_notations }

   This command introduces a method for constructing an infinite object of a
   coinductive type. For example, the stream containing all natural numbers can
   be introduced applying the following method to the number :g:`O` (see
   Section :ref:`coinductive-types` for the definition of :g:`Stream`, :g:`hd`
   and :g:`tl`):

   .. coqtop:: all

      CoFixpoint from (n:nat) : Stream := Seq n (from (S n)).

   Unlike recursive definitions, there is no decreasing argument in a
   co-recursive definition. To be admissible, a method of construction must
   provide at least one extra constructor of the infinite object for each
   iteration. A syntactical guard condition is imposed on co-recursive
   definitions in order to ensure this: each recursive call in the
   definition must be protected by at least one constructor, and only by
   constructors. That is the case in the former definition, where the single
   recursive call of :g:`from` is guarded by an application of :g:`Seq`.
   On the contrary, the following recursive function does not satisfy the
   guard condition:

   .. coqtop:: all

      Fail CoFixpoint filter (p:nat -> bool) (s:Stream) : Stream :=
        if p (hd s) then Seq (hd s) (filter p (tl s)) else filter p (tl s).

   The elimination of co-recursive definition is done lazily, i.e. the
   definition is expanded only when it occurs at the head of an application
   which is the argument of a case analysis expression. In any other
   context, it is considered as a canonical expression which is completely
   evaluated. We can test this using the command :cmd:`Eval`, which computes
   the normal forms of a term:

   .. coqtop:: all

      Eval compute in (from 0).
      Eval compute in (hd (from 0)).
      Eval compute in (tl (from 0)).

   As in the :cmd:`Fixpoint` command, the :n:`with` clause allows simultaneously
   defining several mutual cofixpoints.

   If :n:`@term` is omitted, :n:`@type` is required and Coq enters proof editing mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a constant
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.
