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

.. insertprodn term_if term_if

.. prodn::
   term_if ::= if @term {? {? as @name } return @term100 } then @term else @term

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

More generally, for an inductive type with constructors :n:`@ident__1`
and :n:`@ident__2`, the following terms are equal:

:n:`if @term__0 {? {? as @name } return @term } then @term__1 else @term__2`

:n:`match @term__0 {? {? as @name } return @term } with | @ident__1 {* _ } => @term__1 | @ident__2 {* _ } => @term__2 end`

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

The expression :n:`let ( {*, @ident__i } ) := @term__0 in @term__1`
performs case analysis on :n:`@term__0` whose type must be an
inductive type with exactly one constructor.  The number of variables
:n:`@ident__i` must correspond to the number of arguments of this
contrustor.  Then, in :n:`@term__1`, these variables are bound to the
arguments of the constructor in :n:`@term__0`.  For instance, the
definition

.. coqtop:: reset all

   Definition fst (A B:Set) (H:A * B) := match H with
   | pair x y => x
   end.

can be alternatively written

.. coqtop:: reset all

   Definition fst (A B:Set) (p:A * B) := let (x, _) := p in x.

Notice that reduction is different from regular :g:`let … in …`
construction since it happens only if :n:`@term__0` is in constructor form.
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
   Use the :cmd:`Add` and :cmd:`Remove` commands to update this set.


Printing matching on booleans
+++++++++++++++++++++++++++++

If an inductive type is isomorphic to the boolean type, pattern matching
can be written using ``if`` … ``then`` … ``else`` ….  This table controls
which types are written this way:

.. table:: Printing If @qualid
   :name: Printing If

   Specifies a set of qualids for which pattern matching is displayed using
   ``if`` … ``then`` … ``else`` ….  Use the :cmd:`Add` and :cmd:`Remove`
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
