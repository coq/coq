.. _extendedpatternmatching:

Extended pattern matching
=========================

:Authors: Cristina Cornes and Hugo Herbelin

This section describes the full form of pattern matching in Rocq terms.

.. |rhs| replace:: right hand sides

.. extracted from Gallina extensions chapter

Variants and extensions of :g:`match`
-------------------------------------

.. _mult-match:

Multiple and nested pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The basic version of :g:`match` allows pattern matching on simple
patterns. As an extension, multiple nested patterns or disjunction of
patterns are allowed, as in ML-like languages
(cf. :ref:`multiple-patterns` and :ref:`nested-patterns`).

The extension just acts as a macro that is expanded during parsing
into a sequence of match on simple patterns. Especially, a
construction defined using the extended match is generally printed
under its expanded form (see :flag:`Printing Matching`).

.. _if-then-else:

Pattern-matching on boolean values: the if expression
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. insertprodn term_if term_if

.. prodn::
   term_if ::= if @term {? {? as @name } return @term100 } then @term else @term

For inductive types with exactly two constructors and for pattern matching
expressions that do not depend on the arguments of the constructors, it is possible
to use a ``if … then … else`` notation. For instance, the definition

.. rocqtop:: all

   Definition not (b:bool) :=
   match b with
   | true => false
   | false => true
   end.

can be alternatively written

.. rocqtop:: reset all

   Definition not (b:bool) := if b then false else true.

More generally, for an inductive type with constructors :n:`@ident__1`
and :n:`@ident__2`, the following terms are equal:

:n:`if @term__0 {? {? as @name } return @term } then @term__1 else @term__2`

:n:`match @term__0 {? {? as @name } return @term } with | @ident__1 {* _ } => @term__1 | @ident__2 {* _ } => @term__2 end`

.. example::

  .. rocqtop:: all

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

.. insertprodn destructuring_let destructuring_let

.. prodn::
   destructuring_let ::= let ( {*, @name } ) {? {? as @name } return @term100 } := @term in @term
   | let ' @pattern := @term {? return @term100 } in @term
   | let ' @pattern in @pattern := @term return @term100 in @term


First destructuring let syntax
++++++++++++++++++++++++++++++

.. todo explain that this applies to all of the "let" constructs (Gallina, Ltac1 and Ltac2)
   also add "irrefutable pattern" to the glossary
   note that in Ltac2 an upper case ident is a constructor, lower case is a variable

The expression :n:`let ( {*, @ident__i } ) := @term__0 in @term__1`
performs case analysis on :n:`@term__0` whose type must be an
inductive type with exactly one constructor.  The number of variables
:n:`@ident__i` must correspond to the number of arguments of this
constructor.  Then, in :n:`@term__1`, these variables are bound to the
arguments of the constructor in :n:`@term__0`.  For instance, the
definition

.. rocqtop:: reset all

   Definition fst (A B:Set) (H:A * B) := match H with
   | pair x y => x
   end.

can be alternatively written

.. rocqtop:: reset all

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

.. rocqtop:: reset all

   Definition fst (A B:Set) (p:A*B) := let 'pair x _ := p in x.

This is useful to match deeper inside tuples and also to use notations
for the pattern, as the syntax :g:`let ’p := t in b` allows arbitrary
patterns to do the deconstruction. For example:

.. rocqtop:: all

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

   When this :term:`flag` is on (default), Coq’s printer tries to do such
   limited re-factorization.
   Turning it off tells Rocq to print only simple pattern matching problems
   in the same way as the Rocq kernel handles them.


Factorization of clauses with same right-hand side
++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Printing Factorizable Match Patterns

   When several patterns share the same right-hand side, it is additionally
   possible to share the clauses using disjunctive patterns. Assuming that the
   printing matching mode is on, this :term:`flag` (on by default) tells Rocq's
   printer to try to do this kind of factorization.

Use of a default clause
+++++++++++++++++++++++

.. flag:: Printing Allow Match Default Clause

   When several patterns share the same right-hand side which do not depend on the
   arguments of the patterns, yet an extra factorization is possible: the
   disjunction of patterns can be replaced with a `_` default clause. Assuming that
   the printing matching mode and the factorization mode are on, this :term:`flag` (on by
   default) tells Rocq's printer to use a default clause when relevant.

Printing of wildcard patterns
++++++++++++++++++++++++++++++

.. flag:: Printing Wildcard

   Some variables in a pattern may not occur in the right-hand side of
   the pattern matching clause. When this :term:`flag` is on (default), the
   variables having no occurrences in the right-hand side of the
   pattern matching clause are just printed using the wildcard symbol
   “_”.


Printing of the elimination predicate
+++++++++++++++++++++++++++++++++++++

.. flag:: Printing Synth

   In most of the cases, the type of the result of a matched term is
   mechanically synthesizable. Especially, if the result type does not
   depend of the matched term. When this :term:`flag` is on (default),
   the result type is not printed when Rocq knows that it can re-
   synthesize it.

Printing of hidden subterms
+++++++++++++++++++++++++++

.. flag:: Printing Match All Subterms

   In order to be able to cheaply reconstruct the types of the
   variables bound by `in` and `as`, `match` terms contain the
   polymorphic universe instance and the parameters of the inductive
   which is being matched. When this flag is on (it is off by
   default), this information is displayed as a :term:`volatile cast` around
   the match discriminee.

   When the match relies on :flag:`Definitional UIP`,
   the indices are also subterms of the `match` term and are displayed when this flag is on.
   Otherwise they are not subterms and are displayed as holes (`_`) when this flag is on.

   .. example::

      .. rocqtop:: in

         Polymorphic Inductive eqT@{u} {A:Type@{u}} (a:A) : A -> Type@{u} := reflT : eqT a a.
         Set Definitional UIP.
         Inductive seq {A} (a:A) : A -> SProp := srefl : seq a a.

      .. rocqtop:: all

         Print eqT_rect.
         Print seq_rect.

         Set Printing Match All Subterms.
         Set Printing Universes.

         Print eqT_rect.
         Print seq_rect.

Printing matching on irrefutable patterns
++++++++++++++++++++++++++++++++++++++++++

If an inductive type has just one constructor, pattern matching can be
written using the first destructuring let syntax.

.. table:: Printing Let @qualid

   This :term:`table` specifies a set of qualids for which pattern matching is displayed using a let expression.
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

   This :term:`table` specifies a set of qualids for which pattern matching is displayed using
   ``if`` … ``then`` … ``else`` ….  Use the :cmd:`Add` and :cmd:`Remove`
   commands to update this set.

This example emphasizes what the printing settings offer.

.. example::

     .. rocqtop:: all

       Definition snd (A B:Set) (H:A * B) := match H with
       | pair x y => y
       end.

       Test Printing Let for prod.

       Print snd.

       Remove Printing Let prod.

       Unset Printing Synth.

       Unset Printing Wildcard.

       Print snd.

Conventions about unused pattern-matching variables
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Pattern-matching variables that are not used on the right-hand side of ``=>`` are
considered the sign of a potential error. For instance, it could
result from an undetected misspelled constant constructor. By default,
a warning is issued in such situations.

.. warn:: Unused variable @ident might be a misspelled constructor. Use _ or _@ident to silence this warning.
   :name: Unused variable ‘ident’ might be a misspelled constructor. Use _ or _‘ident’ to silence this warning.

   This indicates that an unused pattern variable :token:`ident`
   occurs in a pattern-matching clause.

   The warning can be deactivated by using a variable name starting
   with ``_`` or by setting ``Set Warnings
   "-unused-pattern-matching-variable"``.

   Here is an example where the warning is activated.

   .. example::

      .. rocqtop:: all warn

         Definition is_zero (o : option nat) := match o with
         | Some _ => true
         | x => false
         end.

Patterns
--------

The full syntax of `match` is presented in :ref:`match_term`.
Identifiers in patterns are either constructor names or variables. Any
identifier that is not the constructor of an inductive or coinductive
type is considered to be a variable. A variable name cannot occur more
than once in a given pattern. It is recommended to start variable
names by a lowercase letter.

If a pattern has the form ``c x`` where ``c`` is a constructor symbol and x
is a linear vector of (distinct) variables, it is called *simple*: it
is the kind of pattern recognized by the basic version of match. On
the opposite, if it is a variable ``x`` or has the form ``c p`` with ``p`` not
only made of variables, the pattern is called *nested*.

A variable pattern matches any value, and the identifier is bound to
that value. The pattern “``_``” (called “don't care” or “wildcard” symbol)
also matches any value, but does not bind anything. It may occur an
arbitrary number of times in a pattern. Alias patterns written
:n:`(@pattern as @ident)` are also accepted. This pattern matches the
same values as :token:`pattern` does and :token:`ident` is bound to the matched
value. A pattern of the form :n:`@pattern | @pattern` is called disjunctive. A
list of patterns separated with commas is also considered as a pattern
and is called *multiple pattern*. However multiple patterns can only
occur at the root of pattern matching equations. Disjunctions of
*multiple patterns* are allowed though.

Since extended ``match`` expressions are compiled into the primitive ones,
the expressiveness of the theory remains the same. Once parsing has finished
only simple patterns remain. The original nesting of the ``match`` expressions
is recovered at printing time. An easy way to see the result
of the expansion is to toggle off the nesting performed at printing
(use here :flag:`Printing Matching`), then by printing the term with :cmd:`Print`
if the term is a :term:`constant`, or using the command :cmd:`Check`.

The extended ``match`` still accepts an optional *elimination predicate*
given after the keyword ``return``. Given a pattern matching expression,
if all the right-hand-sides of ``=>`` have the same
type, then this type can be sometimes synthesized, and so we can omit
the return part. Otherwise the predicate after return has to be
provided, like for the basicmatch.

Let us illustrate through examples the different aspects of extended
pattern matching. Consider for example the function that computes the
maximum of two natural numbers. We can write it in primitive syntax
by:

.. rocqtop:: in

   Fixpoint max (n m:nat) {struct m} : nat :=
     match n with
     | O => m
     | S n' => match m with
               | O => S n'
               | S m' => S (max n' m')
               end
     end.

.. _multiple-patterns:

Multiple patterns
-----------------

Using multiple patterns in the definition of ``max`` lets us write:

.. rocqtop:: in reset

   Fixpoint max (n m:nat) {struct m} : nat :=
       match n, m with
       | O, _ => m
       | S n', O => S n'
       | S n', S m' => S (max n' m')
       end.

which will be compiled into the previous form.

The pattern matching compilation strategy examines patterns from left
to right. A match expression is generated **only** when there is at least
one constructor in the column of patterns. E.g. the following example
does not build a match expression.

.. rocqtop:: all

   Check (fun x:nat => match x return nat with
                       | y => y
                       end).


Aliasing subpatterns
--------------------

We can also use :n:`as @ident` to associate a name to a sub-pattern:

.. rocqtop:: in reset

   Fixpoint max (n m:nat) {struct n} : nat :=
     match n, m with
     | O, _ => m
     | S n' as p, O => p
     | S n', S m' => S (max n' m')
     end.

.. _nested-patterns:

Nested patterns
---------------

Here is now an example of nested patterns:

.. rocqtop:: in

   Fixpoint even (n:nat) : bool :=
     match n with
     | O => true
     | S O => false
     | S (S n') => even n'
     end.

This is compiled into:

.. rocqtop:: all

   Unset Printing Matching.
   Print even.

.. rocqtop:: none

   Set Printing Matching.

In the previous examples patterns do not conflict with, but sometimes
it is comfortable to write patterns that admit a nontrivial
superposition. Consider the boolean function :g:`lef` that given two
natural numbers yields :g:`true` if the first one is less or equal than the
second one and :g:`false` otherwise. We can write it as follows:

.. rocqtop:: in

   Fixpoint lef (n m:nat) {struct m} : bool :=
     match n, m with
     | O, _ => true
     | _, O => false
     | S n, S m => lef n m
     end.

Note that the first and the second multiple pattern overlap because
the couple of values ``O O`` matches both. Thus, what is the result of the
function on those values? To eliminate ambiguity we use the *textual
priority rule:* we consider patterns to be ordered from top to bottom. A
value is matched by the pattern at the ith row if and only if it is
not matched by some pattern from a previous row. Thus in the example, ``O O``
is matched by the first pattern, and so :g:`(lef O O)` yields true.

Another way to write this function is:

.. rocqtop:: in reset

   Fixpoint lef (n m:nat) {struct m} : bool :=
     match n, m with
     | O, _ => true
     | S n, S m => lef n m
     | _, _ => false
     end.

Here the last pattern superposes with the first two. Because of the
priority rule, the last pattern will be used only for values that do
not match neither the first nor the second one.

Terms with useless patterns are not accepted by the system. Here is an
example:

.. rocqtop:: all

   Fail Check (fun x:nat =>
                 match x with
                 | O => true
                 | S _ => false
                 | x => true
                 end).


Disjunctive patterns
--------------------

Multiple patterns that share the same right-hand-side can be
factorized using the notation :n:`{+| {+, @pattern } }`. For
instance, :g:`max` can be rewritten as follows:

.. rocqtop:: in reset

   Fixpoint max (n m:nat) {struct m} : nat :=
     match n, m with
     | S n', S m' => S (max n' m')
     | 0, p | p, 0 => p
     end.

Similarly, factorization of (not necessarily multiple) patterns that
share the same variables is possible by using the notation :n:`{+| @pattern}`.
Here is an example:

.. rocqtop:: in

   Definition filter_2_4 (n:nat) : nat :=
     match n with
     | 2 as m | 4 as m => m
     | _ => 0
     end.


Nested disjunctive patterns are allowed, inside parentheses, with the
notation :n:`({+| @pattern})`, as in:

.. rocqtop:: in

   Definition filter_some_square_corners (p:nat*nat) : nat*nat :=
     match p with
     | ((2 as m | 4 as m), (3 as n | 5 as n)) => (m,n)
     | _ => (0,0)
     end.

About patterns of parametric types
----------------------------------

Parameters in patterns
~~~~~~~~~~~~~~~~~~~~~~

When matching objects of a parametric type, parameters do not bind in
patterns. They must be substituted by “``_``”. Consider for example the
type of polymorphic lists:

.. rocqtop:: in

   Inductive List (A:Set) : Set :=
   | nil : List A
   | cons : A -> List A -> List A.

We can check the function *tail*:

.. rocqtop:: all

   Check
     (fun l:List nat =>
        match l with
        | nil _ => nil nat
        | cons _ _ l' => l'
        end).

When we use parameters in patterns there is an error message:

.. rocqtop:: all

   Fail Check
     (fun l:List nat =>
        match l with
        | nil A => nil nat
        | cons A _ l' => l'
        end).

.. flag:: Asymmetric Patterns

   This :term:`flag` (off by default) removes parameters from constructors in patterns:

.. rocqtop:: all

   Set Asymmetric Patterns.
   Check (fun l:List nat =>
     match l with
     | nil => nil _
     | cons _ l' => l'
     end).
   Unset Asymmetric Patterns.

Implicit arguments in patterns
------------------------------

By default, implicit arguments are omitted in patterns. So we write:

.. rocqtop:: all

   Arguments nil {A}.
   Arguments cons [A] _ _.
   Check
     (fun l:List nat =>
        match l with
        | nil => nil
        | cons _ l' => l'
        end).

But the possibility to use all the arguments is given by “``@``” implicit
explicitations (as for terms, see :ref:`explicit-applications`).

.. rocqtop:: all

   Check
     (fun l:List nat =>
        match l with
        | @nil _ => @nil nat
        | @cons _ _ l' => l'
        end).


.. _matching-dependent:

Matching objects of dependent types
-----------------------------------

The previous examples illustrate pattern matching on objects of non-
dependent types, but we can also use the expansion strategy to
destructure objects of dependent types. Consider the type :g:`listn` of
lists of a certain length:

.. rocqtop:: in reset

   Inductive listn : nat -> Set :=
   | niln : listn 0
   | consn : forall n:nat, nat -> listn n -> listn (S n).


Understanding dependencies in patterns
--------------------------------------

We can define the function length over :g:`listn` by:

.. rocqdoc::

   Definition length (n:nat) (l:listn n) := n.

Just for illustrating pattern matching, we can define it by case
analysis:

.. rocqtop:: in

   Definition length (n:nat) (l:listn n) :=
     match l with
     | niln => 0
     | consn n _ _ => S n
     end.

We can understand the meaning of this definition using the same
notions of usual pattern matching.


When the elimination predicate must be provided
-----------------------------------------------

Dependent pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~

The examples given so far do not need an explicit elimination
predicate because all the |rhs| have the same type and Rocq
succeeds to synthesize it. Unfortunately when dealing with dependent
patterns it often happens that we need to write cases where the types
of the |rhs| are different instances of the elimination predicate. The
function :g:`concat` for :g:`listn` is an example where the branches have
different types and we need to provide the elimination predicate:

.. rocqtop:: in

   Fixpoint concat (n:nat) (l:listn n) (m:nat) (l':listn m) {struct l} :
    listn (n + m) :=
     match l in listn n return listn (n + m) with
     | niln => l'
     | consn n' a y => consn (n' + m) a (concat n' y m l')
     end.

.. rocqtop:: none

   Reset concat.

The elimination predicate is :g:`fun (n:nat) (l:listn n) => listn (n+m)`.
In general if :g:`m` has type :g:`(I q1 … qr t1 … ts)` where :g:`q1, …, qr`
are parameters, the elimination predicate should be of the form :g:`fun y1 … ys x : (I q1 … qr y1 … ys ) => Q`.

In the concrete syntax, it should be written :
``match m as x in (I _ … _ y1 … ys) return Q with … end``.
The variables which appear in the ``in`` and ``as`` clause are new and bounded
in the property :g:`Q` in the return clause. The parameters of the
inductive definitions should not be mentioned and are replaced by ``_``.

Multiple dependent pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Recall that a list of patterns is also a pattern. So, when we
destructure several terms at the same time and the branches have
different types we need to provide the elimination predicate for this
multiple pattern. It is done using the same scheme: each term may be
associated with an ``as`` clause and an ``in`` clause in order to introduce
a dependent product.

For example, an equivalent definition for :g:`concat` (even though the
matching on the second term is trivial) would have been:

.. rocqtop:: in

   Fixpoint concat (n:nat) (l:listn n) (m:nat) (l':listn m) {struct l} :
    listn (n + m) :=
     match l in listn n, l' return listn (n + m) with
     | niln, x => x
     | consn n' a y, x => consn (n' + m) a (concat n' y m x)
     end.

Even without real matching over the second term, this construction can
be used to keep types linked. If :g:`a` and :g:`b` are two :g:`listn` of the same
length, by writing

.. rocqtop:: in

   Check (fun n (a b: listn n) =>
    match a, b with
    | niln, b0 => tt
    | consn n' a y, bS => tt
    end).

we have a copy of :g:`b` in type :g:`listn 0` resp. :g:`listn (S n')`.

.. _match-in-patterns:

Patterns in ``in``
~~~~~~~~~~~~~~~~~~

If the type of the matched term is more precise than an inductive
applied to variables, arguments of the inductive in the ``in`` branch can
be more complicated patterns than a variable.

Moreover, constructors whose types do not follow the same pattern will
become impossible branches. In an impossible branch, you can answer
anything but False_rect unit has the advantage to be subterm of
anything.

To be concrete: the ``tail`` function can be written:

.. rocqtop:: in

   Definition tail n (v: listn (S n)) :=
     match v in listn (S m) return listn m with
     | niln => False_rect unit
     | consn n' a y => y
     end.

and :g:`tail n v` will be subterm of :g:`v`.

Using pattern matching to write proofs
--------------------------------------

In all the previous examples the elimination predicate does not depend
on the object(s) matched. But it may depend and the typical case is
when we write a proof by induction or a function that yields an object
of a dependent type. An example of a proof written using ``match`` is given
in the description of the tactic :tacn:`refine`.

For example, we can write the function :g:`buildlist` that given a natural
number :g:`n` builds a list of length :g:`n` containing zeros as follows:

.. rocqtop:: in

   Fixpoint buildlist (n:nat) : listn n :=
     match n return listn n with
     | O => niln
     | S n => consn n 0 (buildlist n)
     end.

We can also use multiple patterns. Consider the following definition
of the predicate less-equal :g:`Le`:

.. rocqtop:: in

   Inductive LE : nat -> nat -> Prop :=
     | LEO : forall n:nat, LE 0 n
     | LES : forall n m:nat, LE n m -> LE (S n) (S m).

We can use multiple patterns to write the proof of the lemma
:g:`forall (n m:nat), (LE n m) \/ (LE m n)`:

.. rocqtop:: in

   Fixpoint dec (n m:nat) {struct n} : LE n m \/ LE m n :=
     match n, m return LE n m \/ LE m n with
     | O, x => or_introl (LE x 0) (LEO x)
     | x, O => or_intror (LE x 0) (LEO x)
     | S n as n', S m as m' =>
         match dec n m with
         | or_introl h => or_introl (LE m' n') (LES n m h)
         | or_intror h => or_intror (LE n' m') (LES m n h)
         end
     end.

In the example of :g:`dec`, the first match is dependent while the second
is not.

The user can also use match in combination with the tactic :tacn:`refine`
to build incomplete proofs beginning with a :g:`match` construction.


Pattern-matching on inductive objects involving local definitions
-----------------------------------------------------------------

If local definitions (`let :=`) occur in the type of a constructor, then there
are two ways to match on this constructor. Either the local
definitions are skipped and matching is done only on the true
arguments of the constructors, or the bindings for local definitions
can also be caught in the matching.

.. example::

   .. rocqtop:: in reset

      Inductive list : nat -> Set :=
      | nil : list 0
      | cons : forall n:nat, let m := (2 * n) in list m -> list (S (S m)).

   In the next example, the local definition is not caught.

   .. rocqtop:: in

      Fixpoint length n (l:list n) {struct l} : nat :=
        match l with
        | nil => 0
        | cons n l0 => S (length (2 * n) l0)
        end.

   But in this example, it is.

   .. rocqtop:: in

      Fixpoint length' n (l:list n) {struct l} : nat :=
        match l with
        | nil => 0
        | @cons _ m l0 => S (length' m l0)
        end.

.. note:: For a given matching clause, either none of the local
          definitions or all of them can be caught.

.. note:: You can only catch let bindings in mode where you bind all
          variables and so you have to use ``@`` syntax.

.. note:: this feature is incoherent with the fact that parameters
          cannot be caught and consequently is somehow hidden. For example,
          there is no mention of it in error messages.

Pattern-matching and coercions
------------------------------

If a mismatch occurs between the expected type of a pattern and its
actual type, a coercion made from constructors is sought. If such a
coercion can be found, it is automatically inserted around the
pattern.

.. example::

   .. rocqtop:: in

      Inductive I : Set :=
        | C1 : nat -> I
        | C2 : I -> I.

      Coercion C1 : nat >-> I.

   .. rocqtop:: all

      Check (fun x => match x with
                      | C2 O => 0
                      | _ => 0
                      end).


When does the expansion strategy fail?
--------------------------------------

The strategy works very like in ML languages when treating patterns of
non-dependent types. But there are new cases of failure that are due to
the presence of dependencies.

The error messages of the current implementation may be sometimes
confusing. When the tactic fails because patterns are somehow
incorrect then error messages refer to the initial expression. But the
strategy may succeed to build an expression whose sub-expressions are
well typed when the whole expression is not. In this situation the
message makes reference to the expanded expression. We encourage
users, when they have patterns with the same outer constructor in
different equations, to name the variable patterns in the same
positions with the same name. E.g. to write ``(cons n O x) => e1`` and
``(cons n _ x) => e2`` instead of ``(cons n O x) => e1`` and
``(cons n' _ x') => e2``. This helps to maintain certain name correspondence between the
generated expression and the original.

Here is a summary of the error messages corresponding to each
situation:

.. exn:: The constructor @ident expects @natural arguments.
         The variable ident is bound several times in pattern term
         Found a constructor of inductive type term while a constructor of term is expected

   Patterns are incorrect (because constructors are not applied to the correct number of
   arguments, because they are not linear or they are wrongly typed).

.. exn:: Non exhaustive pattern matching.

   The pattern matching is not exhaustive.

.. exn:: The elimination predicate term should be of arity @natural (for non \
         dependent case) or @natural (for dependent case).

   The elimination predicate provided to match has not the expected arity.

.. exn:: Unable to infer a match predicate
         Either there is a type incompatibility or the problem involves dependencies.

   There is a type mismatch between the different branches. The user should
   provide an elimination predicate.
