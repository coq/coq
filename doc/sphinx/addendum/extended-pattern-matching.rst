.. _extendedpatternmatching:

Extended pattern matching
=========================

:Authors: Cristina Cornes and Hugo Herbelin

.. TODO links to figures

This section describes the full form of pattern matching in |Coq| terms.

.. |rhs| replace:: right hand sides

Patterns
--------

The full syntax of match is presented in Figures 1.1 and 1.2.
Identifiers in patterns are either constructor names or variables. Any
identifier that is not the constructor of an inductive or co-inductive
type is considered to be a variable. A variable name cannot occur more
than once in a given pattern. It is recommended to start variable
names by a lowercase letter.

If a pattern has the form ``(c x)`` where ``c`` is a constructor symbol and x
is a linear vector of (distinct) variables, it is called *simple*: it
is the kind of pattern recognized by the basic version of match. On
the opposite, if it is a variable ``x`` or has the form ``(c p)`` with ``p`` not
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
if the term is a constant, or using the command :cmd:`Check`.

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

.. coqtop:: in undo

   Fixpoint max (n m:nat) {struct m} : nat :=
     match n with
     | O => m
     | S n' => match m with
               | O => S n'
               | S m' => S (max n' m')
               end
     end.

Multiple patterns
-----------------

Using multiple patterns in the definition of ``max`` lets us write:

.. coqtop:: in undo

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

.. coqtop:: all

   Check (fun x:nat => match x return nat with
                       | y => y
                       end).


Aliasing subpatterns
--------------------

We can also use :n:`as @ident` to associate a name to a sub-pattern:

.. coqtop:: in undo

   Fixpoint max (n m:nat) {struct n} : nat :=
     match n, m with
     | O, _ => m
     | S n' as p, O => p
     | S n', S m' => S (max n' m')
     end.

Nested patterns
---------------

Here is now an example of nested patterns:

.. coqtop:: in

   Fixpoint even (n:nat) : bool :=
     match n with
     | O => true
     | S O => false
     | S (S n') => even n'
     end.

This is compiled into:

.. coqtop:: all undo

   Unset Printing Matching.
   Print even.

In the previous examples patterns do not conflict with, but sometimes
it is comfortable to write patterns that admit a non trivial
superposition. Consider the boolean function :g:`lef` that given two
natural numbers yields :g:`true` if the first one is less or equal than the
second one and :g:`false` otherwise. We can write it as follows:

.. coqtop:: in undo

   Fixpoint lef (n m:nat) {struct m} : bool :=
     match n, m with
     | O, x => true
     | x, O => false
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

.. coqtop:: in

   Fixpoint lef (n m:nat) {struct m} : bool :=
     match n, m with
     | O, x => true
     | S n, S m => lef n m
     | _, _ => false
     end.

Here the last pattern superposes with the first two. Because of the
priority rule, the last pattern will be used only for values that do
not match neither the first nor the second one.

Terms with useless patterns are not accepted by the system. Here is an
example:

.. coqtop:: all

   Fail Check (fun x:nat =>
                 match x with
                 | O => true
                 | S _ => false
                 | x => true
                 end).


Disjunctive patterns
--------------------

Multiple patterns that share the same right-hand-side can be
factorized using the notation :n:`{+| @mult_pattern}`. For
instance, :g:`max` can be rewritten as follows:

.. coqtop:: in undo

   Fixpoint max (n m:nat) {struct m} : nat :=
     match n, m with
     | S n', S m' => S (max n' m')
     | 0, p | p, 0 => p
     end.

Similarly, factorization of (not necessarily multiple) patterns that
share the same variables is possible by using the notation :n:`{+| @pattern}`.
Here is an example:

.. coqtop:: in

   Definition filter_2_4 (n:nat) : nat :=
     match n with
     | 2 as m | 4 as m => m
     | _ => 0
     end.


Here is another example using disjunctive subpatterns.

.. coqtop:: in

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

.. coqtop:: in

   Inductive List (A:Set) : Set :=
   | nil : List A
   | cons : A -> List A -> List A.

We can check the function *tail*:

.. coqtop:: all

   Check
     (fun l:List nat =>
        match l with
        | nil _ => nil nat
        | cons _ _ l' => l'
        end).

When we use parameters in patterns there is an error message:

.. coqtop:: all

   Fail Check
     (fun l:List nat =>
        match l with
        | nil A => nil nat
        | cons A _ l' => l'
        end).

.. flag:: Asymmetric Patterns

   This flag (off by default) removes parameters from constructors in patterns:

.. coqtop:: all

   Set Asymmetric Patterns.
   Check (fun l:List nat =>
     match l with
     | nil => nil
     | cons _ l' => l'
     end).
   Unset Asymmetric Patterns.

Implicit arguments in patterns
------------------------------

By default, implicit arguments are omitted in patterns. So we write:

.. coqtop:: all

   Arguments nil [A].
   Arguments cons [A] _ _.
   Check
     (fun l:List nat =>
        match l with
        | nil => nil
        | cons _ l' => l'
        end).

But the possibility to use all the arguments is given by “``@``” implicit
explicitations (as for terms 2.7.11).

.. coqtop:: all

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

.. coqtop:: in reset

   Inductive listn : nat -> Set :=
   | niln : listn 0
   | consn : forall n:nat, nat -> listn n -> listn (S n).


Understanding dependencies in patterns
--------------------------------------

We can define the function length over :g:`listn` by:

.. coqtop:: in

   Definition length (n:nat) (l:listn n) := n.

Just for illustrating pattern matching, we can define it by case
analysis:

.. coqtop:: in

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
predicate because all the |rhs| have the same type and Coq
succeeds to synthesize it. Unfortunately when dealing with dependent
patterns it often happens that we need to write cases where the types
of the |rhs| are different instances of the elimination predicate. The
function :g:`concat` for :g:`listn` is an example where the branches have
different types and we need to provide the elimination predicate:

.. coqtop:: in

   Fixpoint concat (n:nat) (l:listn n) (m:nat) (l':listn m) {struct l} :
    listn (n + m) :=
     match l in listn n return listn (n + m) with
     | niln => l'
     | consn n' a y => consn (n' + m) a (concat n' y m l')
     end.

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
associated to an ``as`` clause and an ``in`` clause in order to introduce
a dependent product.

For example, an equivalent definition for :g:`concat` (even though the
matching on the second term is trivial) would have been:

.. coqtop:: in

   Fixpoint concat (n:nat) (l:listn n) (m:nat) (l':listn m) {struct l} :
    listn (n + m) :=
     match l in listn n, l' return listn (n + m) with
     | niln, x => x
     | consn n' a y, x => consn (n' + m) a (concat n' y m x)
     end.

Even without real matching over the second term, this construction can
be used to keep types linked. If :g:`a` and :g:`b` are two :g:`listn` of the same
length, by writing

.. coqtop:: in

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

.. coqtop:: in

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

.. coqtop:: in

   Fixpoint buildlist (n:nat) : listn n :=
     match n return listn n with
     | O => niln
     | S n => consn n 0 (buildlist n)
     end.

We can also use multiple patterns. Consider the following definition
of the predicate less-equal :g:`Le`:

.. coqtop:: in

   Inductive LE : nat -> nat -> Prop :=
     | LEO : forall n:nat, LE 0 n
     | LES : forall n m:nat, LE n m -> LE (S n) (S m).

We can use multiple patterns to write the proof of the lemma
:g:`forall (n m:nat), (LE n m) \/ (LE m n)`:

.. coqtop:: in

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

The user can also use match in combination with the tactic :tacn:`refine` (see
Section 8.2.3) to build incomplete proofs beginning with a match
construction.


Pattern-matching on inductive objects involving local definitions
-----------------------------------------------------------------

If local definitions occur in the type of a constructor, then there
are two ways to match on this constructor. Either the local
definitions are skipped and matching is done only on the true
arguments of the constructors, or the bindings for local definitions
can also be caught in the matching.

.. example::

   .. coqtop:: in

      Inductive list : nat -> Set :=
      | nil : list 0
      | cons : forall n:nat, let m := (2 * n) in list m -> list (S (S m)).

   In the next example, the local definition is not caught.

   .. coqtop:: in

      Fixpoint length n (l:list n) {struct l} : nat :=
        match l with
        | nil => 0
        | cons n l0 => S (length (2 * n) l0)
        end.

   But in this example, it is.

   .. coqtop:: in

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

   .. coqtop:: in

      Inductive I : Set :=
        | C1 : nat -> I
        | C2 : I -> I.

      Coercion C1 : nat >-> I.

   .. coqtop:: all

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

.. exn:: The constructor @ident expects @num arguments.

   The variable ident is bound several times in pattern termFound a constructor
   of inductive type term while a constructor of term is expectedPatterns are
   incorrect (because constructors are not applied to the correct number of the
   arguments, because they are not linear or they are wrongly typed).

.. exn:: Non exhaustive pattern matching.

   The pattern matching is not exhaustive.

.. exn:: The elimination predicate term should be of arity @num (for non \
         dependent case) or @num (for dependent case).

   The elimination predicate provided to match has not the expected arity.

.. exn:: Unable to infer a match predicate
         Either there is a type incompatibility or the problem involves dependencies.

   There is a type mismatch between the different branches. The user should
   provide an elimination predicate.
