.. _thessreflectprooflanguage:

------------------------------
 The |SSR| proof language
------------------------------

:Authors: Georges Gonthier, Assia Mahboubi, Enrico Tassi


Introduction
------------

This chapter describes a set of tactics known as |SSR| originally
designed to provide support for the so-called *small scale reflection*
proof methodology. Despite the original purpose, this set of tactics is
of general interest and is available in Rocq starting from version 8.7.

|SSR| was developed independently of the tactics described in
Chapter :ref:`tactics`. Indeed the scope of the tactics part of |SSR| largely
overlaps with the standard set of tactics. Eventually the overlap will
be reduced in future releases of Rocq.

Proofs written in |SSR| typically look quite different from the
ones written using only tactics as per Chapter :ref:`tactics`. We try to
summarise here the most “visible” ones in order to help the reader
already accustomed to the tactics described in Chapter :ref:`tactics` to read
this chapter.

The first difference between the tactics described in this chapter and the
tactics described in Chapter :ref:`tactics` is the way hypotheses are managed
(we call this *bookkeeping*). In Chapter :ref:`tactics` the most common
approach is to avoid moving explicitly hypotheses back and forth between the
context and the conclusion of the goal. On the contrary, in |SSR| all
bookkeeping is performed on the conclusion of the goal, using for that
purpose a couple of syntactic constructions behaving similar to tacticals
(and often named as such in this chapter). The ``:`` tactical moves hypotheses
from the context to the conclusion, while ``=>`` moves hypotheses from the
conclusion to the context, and ``in`` moves back and forth a hypothesis from the
context to the conclusion for the time of applying an action to it.

While naming hypotheses is commonly done by means of an ``as`` clause in the
basic model of Chapter :ref:`tactics`, it is here to ``=>`` that this task is
devoted. Tactics frequently leave new assumptions in the conclusion, and are
often followed by ``=>`` to explicitly name them. While generalizing the
goal is normally not explicitly needed in Chapter :ref:`tactics`, it is an
explicit operation performed by ``:``.

.. seealso:: :ref:`bookkeeping_ssr`

Besides the difference of bookkeeping model, this chapter includes
specific tactics that have no explicit counterpart in Chapter :ref:`tactics`
such as tactics to mix forward steps and generalizations as
:tacn:`generally have` or :tacn:`without loss`.

|SSR| adopts the point of view that rewriting, definition
expansion and partial evaluation participate all to a same concept of
rewriting a goal in a larger sense. As such, all these functionalities
are provided by the :tacn:`rewrite <rewrite (ssreflect)>` tactic.

|SSR| includes a little language of patterns to select subterms in
tactics or tacticals where it matters. Its most notable application is
in the :tacn:`rewrite <rewrite (ssreflect)>` tactic, where patterns are
used to specify where the rewriting step has to take place.

Finally, |SSR| supports so-called reflection steps, typically
allowing to switch back and forth between the computational view and
logical view of a concept.

To conclude, it is worth mentioning that |SSR| tactics can be mixed
with non-|SSR| tactics in the same proof, or in the same Ltac
expression. The few exceptions to this statement are described in
section :ref:`compatibility_issues_ssr`.


Acknowledgments
~~~~~~~~~~~~~~~

The authors would like to thank Frédéric Blanqui, François Pottier and
Laurence Rideau for their comments and suggestions.


Usage
-----


Getting started
~~~~~~~~~~~~~~~

To be available, the tactics presented in this manual need the
following minimal set of libraries to be loaded: ``ssreflect.v``,
``ssrfun.v`` and ``ssrbool.v``.
Moreover, these tactics come with a methodology
specific to the authors of |SSR| and which requires a few options
to be set in a different way than in their default way. All in all,
this corresponds to working in the following context:

.. rocqtop:: in

   From Corelib Require Import ssreflect ssrfun ssrbool.
   Set Implicit Arguments.
   Unset Strict Implicit.
   Unset Printing Implicit Defensive.

.. seealso::
   :flag:`Implicit Arguments`, :flag:`Strict Implicit`,
   :flag:`Printing Implicit Defensive`

.. _compatibility_issues_ssr:


Compatibility issues
~~~~~~~~~~~~~~~~~~~~

Requiring the above modules creates an environment that is mostly
compatible with the rest of Rocq, up to a few discrepancies.


+ New keywords (``is``) might clash with variable, constant, tactic or
  tactical names, or with quasi-keywords in tactic or
  notation commands.
+ New tactic(al)s names (:tacn:`last`, :tacn:`done`, :tacn:`have`, :tacn:`suffices`,
  :tacn:`suff`, :tacn:`without loss`, :tacn:`wlog`, :tacn:`congr`, :tacn:`unlock`)
  might clash with user tactic names.
+ Identifiers with both leading and trailing ``_``, such as ``_x_``, are
  reserved by |SSR| and cannot appear in scripts.
+ The extensions to the :tacn:`rewrite` tactic are partly incompatible with those
  available in current versions of Rocq; in particular, ``rewrite .. in
  (type of k)`` or ``rewrite .. in *`` or any other variant of :tacn:`rewrite`
  will not work, and the |SSR| syntax and semantics for occurrence selection
  and rule chaining are different. Use an explicit rewrite direction
  (``rewrite <- …`` or ``rewrite -> …``) to access the Rocq rewrite tactic.
+ New symbols (``//``, ``/=``, ``//=``) might clash with adjacent
  existing symbols.
  This can be avoided by inserting white spaces.
+ New constant and theorem names might clash with the user theory.
  This can be avoided by not importing all of |SSR|:

  .. rocqtop:: in

     From Corelib Require ssreflect.
     Import ssreflect.SsrSyntax.

  Note that the full
  syntax of |SSR|’s rewrite and reserved identifiers are enabled
  only if the ssreflect module has been required and if ``SsrSyntax`` has
  been imported. Thus a file that requires (without importing) ``ssreflect``
  and imports ``SsrSyntax`` can be required and imported without
  automatically enabling |SSR|’s extended rewrite syntax and
  reserved identifiers.
+ Some user notations (in particular, defining an infix ``;``) might
  interfere with the "open term", parenthesis-free syntax of tactics
  such as :tacn:`have`, :tacn:`set (ssreflect)` and :tacn:`pose (ssreflect)`.
+ The generalization of ``if`` statements to non-Boolean conditions is turned off
  by |SSR|, because it is mostly subsumed by Coercion to ``bool`` of the
  ``sumXXX`` types (declared in ``ssrfun.v``) and the
  :n:`if @term is @pattern then @term else @term` construct
  (see :ref:`pattern_conditional_ssr`).  To use the
  generalized form, turn off the |SSR| Boolean ``if`` notation using the command:
  ``Close Scope boolean_if_scope``.
+ The following flags can be unset to make |SSR| more compatible with
  parts of Rocq.

.. flag:: SsrRewrite

   Controls whether the incompatible rewrite syntax is enabled (the default).
   Disabling the :term:`flag` makes the syntax compatible with other parts of Rocq.

.. flag:: SsrIdents

   Controls whether tactics can refer to |SSR|-generated variables that are
   in the form _xxx_.  Scripts with explicit references to such variables
   are fragile; they are prone to failure if the proof is later modified or
   if the details of variable name generation change in future releases of Rocq.

   The default is on, which gives an error message when the user tries to
   create such identifiers.  Disabling the :term:`flag` generates a warning instead,
   increasing compatibility with other parts of Rocq.

Gallina extensions
--------------------

Small-scale reflection makes an extensive use of the programming
subset of Gallina, Coq’s logical specification language. This subset
is quite suited to the description of functions on representations,
because it closely follows the well-established design of the ML
programming language. The |SSR| extension provides three additions
to Gallina, for pattern assignment, pattern testing, and polymorphism;
these mitigate minor but annoying discrepancies between Gallina and
ML.


Pattern assignment
~~~~~~~~~~~~~~~~~~

The |SSR| extension provides the following construct for
irrefutable pattern matching, that is, destructuring assignment:

.. prodn::
   term += let: @pattern := @term in @term

Note the colon ``:`` after the ``let`` keyword, which avoids any ambiguity
with a function definition or Coq’s basic destructuring let. The ``let:``
construct differs from the latter as follows.


+ The pattern can be nested (deep pattern matching); in particular,
  this allows expression of the form:

.. rocqdoc::

   let: exist (x, y) p_xy := Hp in … .

+ The destructured constructor is explicitly given in the pattern, and
  is used for type inference.

  .. example::

    .. rocqtop:: reset none

       From Corelib Require Import ssreflect.
       Set Implicit Arguments.
       Unset Strict Implicit.
       Unset Printing Implicit Defensive.

    .. rocqtop:: all

       Definition f u := let: (m, n) := u in m + n.
       Check f.

    Using :g:`let:`, Rocq infers a type for :g:`f`,
    whereas with a usual ``let`` the same term requires an extra type
    annotation in order to type check.

    .. rocqtop:: reset all

       Fail Definition f u := let (m, n) := u in m + n.


The ``let:`` construct is just (more legible) notation for the primitive
Gallina expression :n:`match @term with @pattern => @term end`.

The |SSR| destructuring assignment supports all the dependent
match annotations; the full syntax is

.. prodn::
   term += let: @pattern {? as @ident} {? in @pattern} := @term {? return @term} in @term

where the second :token:`pattern` and the second :token:`term` are *types*.

When the ``as`` and ``return`` keywords are both present, then :token:`ident` is bound
in both the second :token:`pattern` and the second :token:`term`; variables
in the optional type :token:`pattern` are bound only in the second term, and
other variables in the first  :token:`pattern` are bound only in the third
:token:`term`, however.


.. _pattern_conditional_ssr:

Pattern conditional
~~~~~~~~~~~~~~~~~~~

The following construct can be used for a refutable pattern matching,
that is, pattern testing:

.. prodn::
   term += if @term is @pattern then @term else @term

Although this construct is not strictly ML (it does exist in variants
such as the pattern calculus or the ρ-calculus), it turns out to be
very convenient for writing functions on representations, because most
such functions manipulate simple data types such as Peano integers,
options, lists, or binary trees, and the pattern conditional above is
almost always the right construct for analyzing such simple types. For
example, the null and all list function(al)s can be defined as follows:

.. example::

    .. rocqtop:: reset none

       From Corelib Require Import ssreflect.
       Set Implicit Arguments.
       Unset Strict Implicit.
       Unset Printing Implicit Defensive.
       Section Test.

   .. rocqtop:: all

      Variable d: Set.
      Definition null (s : list d) :=
        if s is nil then true else false.
      Variable a : d -> bool.
      Fixpoint all (s : list d) : bool :=
        if s is cons x s' then a x && all s' else true.

The pattern conditional also provides a notation for destructuring
assignment with a refutable pattern, adapted to the pure functional
setting of Gallina, which lacks a ``Match_Failure`` exception.

Like ``let:`` above, the ``if…is`` construct is just (more legible) notation
for the primitive Gallina expression
:n:`match @term with @pattern => @term | _ => @term end`.

Similarly, it will always be displayed as the expansion of this form
in terms of primitive match expressions (where the default expression
may be replicated).

Explicit pattern testing also largely subsumes the generalization of
the ``if`` construct to all binary data types; compare
:n:`if @term is inl _ then @term else @term` and
:n:`if @term then @term else @term`.

The latter appears to be marginally shorter, but it is quite
ambiguous, and indeed often requires an explicit annotation
``(term : {_} + {_})`` to type check, which evens the character count.

Therefore, |SSR| restricts by default the condition of a plain ``if``
construct to the standard ``bool`` type; this avoids spurious type
annotations.

.. example::

   .. rocqtop:: all

      Definition orb b1 b2 := if b1 then true else b2.

As pointed out in Section :ref:`compatibility_issues_ssr`,
this restriction can be removed with
the command:

``Close Scope boolean_if_scope.``

Like ``let:`` above, the ``if-is-then-else``
construct supports
the dependent match annotations:

.. prodn::
   term += if @term is @pattern as @ident in @pattern return @term then @term else @term

As in ``let:``, the variable :token:`ident` (and those in the type pattern)
are bound in the second :token:`term`; :token:`ident` is also bound in the
third :token:`term` (but not in the fourth :token:`term`), while the
variables in the first :token:`pattern` are bound only in the third
:token:`term`.

Another variant allows to treat the ``else`` case first:

.. prodn::
   term += if @term isn't @pattern then @term else @term

Note that :token:`pattern` eventually binds variables in the third
:token:`term` and not in the second :token:`term`.

.. _parametric_polymorphism_ssr:

Parametric polymorphism
~~~~~~~~~~~~~~~~~~~~~~~

Unlike ML, polymorphism in core Gallina is explicit: the type
parameters of polymorphic functions must be declared explicitly, and
supplied at each point of use. However, Rocq provides two features to
suppress redundant parameters.


+ Sections are used to provide (possibly implicit) parameters for a
  set of definitions.
+ Implicit arguments declarations are used to tell Rocq to use type
  inference to deduce some parameters from the context at each point of
  call.


The combination of these features provides a fairly good emulation of
ML-style polymorphism, but unfortunately this emulation breaks down
for higher-order programming. Implicit arguments are indeed not
inferred at all points of use, but only at points of call, leading to
expressions such as

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.
      Section Test.
      Variable T : Type.
      Variable null : forall T : Type, T -> bool.
      Variable all : (T -> bool) -> list T -> bool.

   .. rocqtop:: all

      Definition all_null (s : list T) := all (@null T) s.

Unfortunately, such higher-order expressions are quite frequent in
representation functions, especially those that use Rocq's
``Structures`` to emulate Haskell typeclasses.

Therefore, |SSR| provides a variant of Rocq's implicit argument
declaration, which causes Rocq to fill in some implicit parameters at
each point of use; e.g., the above definition can be written:

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.
     Variable T : Type.
     Variable null : forall T : Type, T -> bool.
     Variable all : (T -> bool) -> list T -> bool.


  .. rocqtop:: all

     Prenex Implicits null.
     Definition all_null (s : list T) := all null s.

Better yet, it can be omitted entirely, since :g:`all_null s` isn’t much of
an improvement over :g:`all null s`.

The syntax of the new declaration is

.. cmd:: Prenex Implicits {+ @ident__i}

   This command checks that each :n:`@ident__i` is the name of a functional
   constant, whose implicit arguments are prenex, i.e., the first
   :math:`n_i > 0` arguments of :n:`@ident__i` are implicit; then it assigns
   ``Maximal Implicit`` status to these arguments.

   As these prenex implicit arguments are ubiquitous and have often large
   display strings, it is strongly recommended to change the default
   display settings of Rocq so that they are not printed (except after
   a ``Set Printing All`` command). All |SSR| library files thus start
   with the incantation

   .. rocqdoc::

      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.


Anonymous arguments
~~~~~~~~~~~~~~~~~~~

When in a definition, the type of a certain argument is mandatory, but
not its name, one usually uses “arrow” abstractions for prenex
arguments, or the ``(_ : term)`` syntax for inner arguments. In |SSR|,
the latter can be replaced by the open syntax ``of term`` or
(equivalently) ``& term``, which are both syntactically equivalent to a
``(_ : term)`` expression. This feature almost behaves as the
following extension of the binder syntax:

.. prodn::
   binder += {| & @term | of @term }

Caveat: ``& T`` and ``of T`` abbreviations have to appear at the end
of a binder list. For instance, the usual two-constructor polymorphic
type list, i.e., the one of the standard ``List`` library, can be
defined by the following declaration:

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Inductive list (A : Type) : Type := nil | cons of A & list A.


Wildcards
~~~~~~~~~

The terms passed as arguments to |SSR| tactics can contain
*holes*, materialized by wildcards ``_``. Since |SSR| allows a more
powerful form of type inference for these arguments, it enhances the
possibilities of using such wildcards. These holes are in particular
used as a convenient shorthand for abstractions, especially in local
definitions or type expressions.

Wildcards may be interpreted as abstractions (see for example Sections
:ref:`definitions_ssr` and :ref:`structure_ssr`), or their content can be
inferred from the whole context of the goal (see for example Section
:ref:`abbreviations_ssr`).


.. _definitions_ssr:

Definitions
~~~~~~~~~~~

.. tacn:: pose
   :name: pose (ssreflect)

   This tactic allows to add a defined constant to a proof context.
   |SSR| generalizes this tactic in several ways. In particular, the
   |SSR| :tacn:`pose (ssreflect)` tactic supports *open syntax*: the body of the
   definition does not need surrounding parentheses. For instance:

.. rocqdoc::

   pose t := x + y.

is a valid tactic expression.

The :tacn:`pose (ssreflect)` tactic is also improved for the local definition of higher-order terms. 
Local definitions of functions can use the same syntax as
global ones.
For example, the tactic :tacn:`pose (ssreflect)` supports parameters:

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

   .. rocqtop:: all

      Lemma test : True.
      pose f x y := x + y.

The |SSR| :tacn:`pose (ssreflect)` tactic also supports (co)fixpoints, by providing
the local counterpart of the ``Fixpoint f := …`` and ``CoFixpoint f := …``
constructs. For instance, the following tactic:

.. rocqdoc::

   pose fix f (x y : nat) {struct x} : nat :=
     if x is S p then S (f p y) else 0.

defines a local fixpoint ``f``, which mimics the standard plus operation
on natural numbers.

Similarly, local cofixpoints can be defined by a tactic of the form:

.. rocqdoc::

   pose cofix f (arg : T) := … .

The possibility to include wildcards in the body of the definitions
offers a smooth way of defining local abstractions. The type of
“holes” is guessed by type inference, and the holes are abstracted.
For instance the tactic:

.. rocqdoc::

   pose f := _ + 1.

is shorthand for:

.. rocqdoc::

   pose f n := n + 1.

When the local definition of a function involves both arguments and
holes, hole abstractions appear first. For instance, the tactic:

.. rocqdoc::

   pose f x := x + _.

is shorthand for:

.. rocqdoc::

   pose f n x := x + n.

The interaction of the :tacn:`pose (ssreflect)` tactic with the interpretation of implicit
arguments results in a powerful and concise syntax for local
definitions involving dependent types. For instance, the tactic:

.. rocqdoc::

   pose f x y := (x, y).

adds to the context the local definition:

.. rocqdoc::

   pose f (Tx Ty : Type) (x : Tx) (y : Ty) := (x, y).

The generalization of wildcards makes the use of the :tacn:`pose (ssreflect)` tactic
resemble ML-like definitions of polymorphic functions.


.. _abbreviations_ssr:


Abbreviations
~~~~~~~~~~~~~

.. tacn:: set @ident {? : @term } := {? @occ_switch } @term
   :name: set (ssreflect)

   The |SSR| ``set`` tactic performs abbreviations; it introduces a
   defined constant for a subterm appearing in the goal and/or in the
   context.

   |SSR| extends the :tacn:`set` tactic by supplying:

   + an open syntax, similarly to the :tacn:`pose (ssreflect)` tactic;
   + a more aggressive matching algorithm;
   + an improved interpretation of wildcards, taking advantage of the
     matching algorithm;
   + an improved occurrence selection mechanism allowing to abstract only
     selected occurrences of a term.

.. prodn::
   occ_switch ::= { {? {| + | - } } {* @natural } }

where:

+ :token:`ident` is a fresh identifier chosen by the user.
+ :token:`term` 1 is an optional type annotation. The type annotation :token:`term` 1
  can be given in open syntax (no surrounding parentheses). If no
  :token:`occ_switch` (described hereafter) is present,
  it is also the case for the second :token:`term`.
  On the other hand, in the presence of :token:`occ_switch`, parentheses
  surrounding the second :token:`term` are mandatory.
+ In the occurrence switch :token:`occ_switch`, if the first element of the
  list is a natural, this element should be a number, and not an Ltac
  variable. The empty list ``{}`` is not interpreted as a valid occurrence
  switch; it is rather used as a flag to signal the intent of the user to
  clear the name following it (see :ref:`ssr_rewrite_occ_switch` and
  :ref:`introduction_ssr`).

The tactic:

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.
      Axiom f : nat -> nat.

   .. rocqtop:: all

      Lemma test x :  f x + f x = f x.
      set t := f _.

   .. rocqtop:: all restart

      set t := {2}(f _).


The type annotation may contain wildcards, which will be filled
with appropriate values by the matching process.

The tactic first tries to find a subterm of the goal matching
the second :token:`term`
(and its type), and stops at the first subterm it finds. Then
the occurrences of this subterm selected by the optional :token:`occ_switch`
are replaced by :token:`ident` and a definition :n:`@ident := @term`
is added to the
context. If no :token:`occ_switch` is present, then all the occurrences are
abstracted.


Matching
````````

The matching algorithm compares a pattern :token:`term` with a subterm of the
goal by comparing their heads and then pairwise unifying their
arguments (modulo conversion). Head symbols match under the following
conditions.


+ If the head of :token:`term` is a constant, then it should be syntactically
  equal to the head symbol of the subterm.
+ If this head is a projection of a canonical structure, then
  canonical structure equations are used for the matching.
+ If the head of :token:`term` is *not* a constant, the subterm should have the
  same structure (λ abstraction, ``let…in`` structure, etc.).
+ If the head of :token:`term` is a hole, the subterm should have at least as
  many arguments as :token:`term`.

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

   .. rocqtop:: all

      Lemma test (x y z : nat) :  x + y = z.
      set t := _ x.

+ In the special case where :token:`term` is of the form
  ``(let f := t0 in f) t1 … tn`` , then the pattern :token:`term` is treated
  as ``(_ t1 … tn)``. For each
  subterm in the goal having the form ``(A u1 … um)`` with m ≥ n, the
  matching algorithm successively tries to find the largest partial
  application ``(A u1 … uj)`` convertible to the head ``t0`` of :token:`term`.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.

     .. rocqtop:: all

        Lemma test : (let f x y z := x + y + z in f 1) 2 3 = 6.
        set t := (let g y z := S y + z in g) 2.

  The notation ``unkeyed`` defined in ``ssreflect.v`` is a shorthand for
  the degenerate term ``let x := … in x``.

Moreover:

+ Multiple holes in :token:`term` are treated as independent placeholders.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.

     .. rocqtop:: all

        Lemma test x y z : x + y = z.
        set t := _ + _.

+ The type of the subterm matched should fit the type (possibly casted
  by some type annotations) of the pattern :token:`term`.
+ The replacement of the subterm found by the instantiated pattern
  should not capture variables. In the example above, ``x`` is bound
  and should not be captured.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.

     .. rocqtop:: all

        Lemma test : forall x : nat, x + 1 = 0.
        Fail set t := _ + 1.

+ Typeclass inference should fill in any residual hole, but matching
  should never assign a value to a global existential variable.


.. _occurrence_selection_ssr:

Occurrence selection
````````````````````

|SSR| provides a generic syntax for the selection of occurrences
by their position indexes. These *occurrence switches* are shared by
all |SSR| tactics that require control on subterm selection like
rewriting, generalization, …

An *occurrence switch* can be:

+ A list of natural numbers ``{+ n1 … nm}``
  of occurrences affected by the tactic.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.
        Axiom f : nat -> nat.

     .. rocqtop:: all

        Lemma test : f 2 + f 8 = f 2 + f 2.
        set x := {+1 3}(f 2).

  Notice that some occurrences of a given term may be
  hidden to the user, for example because of a notation. Setting the
  :flag:`Printing All` flag causes these hidden occurrences to
  be shown when the term is displayed.  This setting
  should be used to find the correct coding of the occurrences to be
  selected [#1]_.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.

     .. rocqtop:: all

        Notation "a < b":= (le (S a) b).
        Lemma test x y : x < y -> S x < S y.
        set t := S x.

+ A list of natural numbers ``{n1 … nm}``.
  This is equivalent to the previous ``{+ n1 … nm}``, but the list
  should start with a number, and not with an Ltac variable.
+ A list ``{- n1 … nm}`` of occurrences *not* to be affected by the
  tactic.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.
        Axiom f : nat -> nat.

     .. rocqtop:: all

        Lemma test : f 2 + f 8 = f 2 + f 2.
        set x := {-2}(f 2).


  Note that, in this goal, it behaves like ``set x := {1 3}(f 2).``
+ In particular, the switch ``{+}`` selects *all* the occurrences. This
  switch is useful to turn off the default behavior of a tactic that
  automatically clears some assumptions (see Section :ref:`discharge_ssr` for
  instance).
+ The switch ``{-}`` imposes that *no* occurrences of the term should be
  affected by the tactic. The tactic: ``set x := {-}(f 2).`` leaves the goal
  unchanged and adds the definition ``x := f 2`` to the context. This kind
  of tactic may be used to take advantage of the power of the matching
  algorithm in a local definition, instead of copying large terms by
  hand.

It is important to remember that matching *precedes* occurrence
selection.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.

     .. rocqtop:: all

        Lemma test x y z : x + y = x + y + z.
        set a := {2}(_ + _).

Hence, in the following goal, the same tactic fails since there is
only one occurrence of the selected term.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.

     .. rocqtop:: all

        Lemma test x y z : (x + y) + (z + z) = z + z.
        Fail set a := {2}(_ + _).


.. _basic_localization_ssr:

Basic localization
~~~~~~~~~~~~~~~~~~

It is possible to define an abbreviation for a term appearing in the
context of a goal thanks to the ``in`` tactical.

.. tacv:: set @ident := @term in {+ @ident}

   This variant of :tacn:`set <set (ssreflect)>` introduces a defined constant
   called :token:`ident` in the context, and folds it in
   the context entries mentioned on the right hand side of ``in``.
   The body of :token:`ident` is the first subterm matching these context
   entries (taken in the given order).

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.

     .. rocqtop:: all

        Lemma test x t (Hx : x = 3) : x + t = 4.
        set z := 3 in Hx.

.. tacv:: set @ident := @term in {+ @ident} *

   This variant matches :token:`term` and then folds :token:`ident` similarly
   in all the given context entries but also folds :token:`ident` in the goal.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.

     .. rocqtop:: all

        Lemma test x t (Hx : x = 3) : x + t = 4.
        set z := 3 in Hx * .

     Indeed, remember that 4 is just a notation for (S 3).

The use of the ``in`` tactical is not limited to the localization of
abbreviations: for a complete description of the ``in`` tactical, see
Section :ref:`bookkeeping_ssr` and :ref:`localization_ssr`.


.. _basic_tactics_ssr:

Basic tactics
-------------

A sizable fraction of proof scripts consists of steps that do not
"prove" anything new, but instead perform menial bookkeeping tasks
such as selecting the names of constants and assumptions or splitting
conjuncts. Although they are logically trivial, bookkeeping steps are
extremely important because they define the structure of the data-flow
of a proof script. This is especially true for reflection-based
proofs, which often involve large numbers of constants and
assumptions. Good bookkeeping consists in always explicitly declaring
(i.e., naming) all new constants and assumptions in the script, and
systematically pruning irrelevant constants and assumptions in the
context. This is essential in the context of an interactive
development environment (IDE), because it facilitates navigating the
proof, allowing to instantly "jump back" to the point at which a
questionable assumption was added, and to find relevant assumptions by
browsing the pruned context. While novice or casual Rocq users may find
the automatic name selection feature convenient, the usage of such a
feature severely undermines the readability and maintainability of
proof scripts, much like automatic variable declaration in programming
languages. The |SSR| tactics are therefore designed to support
precise bookkeeping and to eliminate name generation heuristics. The
bookkeeping features of |SSR| are implemented as tacticals (or
pseudo-tacticals), shared across most |SSR| tactics, and thus form
the foundation of the |SSR| proof language.


.. _bookkeeping_ssr:

Bookkeeping
~~~~~~~~~~~

During the course of a proof, Rocq always presents the user with a
*sequent* whose general form is::

  ci : Ti
  …
  dj := ej : Tj
  …
  Fk : Pk
  …
  =================
  forall (xl : Tl) …,
  let ym := bm in … in
  Pn -> … -> C

The *goal* to be proved appears below the double line; above the line
is the *context* of the sequent, a set of declarations of *constants*
``ci`` , *defined constants* ``dj`` , and *facts* ``Fk`` that can be used to
prove the goal (usually, ``Ti`` , ``Tj : Type`` and ``Pk : Prop``).
The various
kinds of declarations can come in any order. The top part of the
context consists of declarations produced by the Section
commands ``Variable``, ``Let``, and ``Hypothesis``.
This *section context* is never
affected by the |SSR| tactics: they only operate on the lower part
— the *proof context*. As in the figure above, the goal often
decomposes into a series of (universally) quantified *variables*
``(xl : Tl)``, local *definitions*
``let ym := bm in``, and *assumptions*
``Pn ->``,
and a *conclusion* ``C`` (as in the context, variables, definitions, and
assumptions can appear in any order). The conclusion is what actually
needs to be proved — the rest of the goal can be seen as a part of the
proof context that happens to be “below the line”.

However, although they are logically equivalent, there are fundamental
differences between constants and facts, on the one hand, and variables
and assumptions, on the other. Constants and facts are *unordered*,
but *named* explicitly in the proof text; variables and assumptions
are *ordered*, but *unnamed*: the display names of variables may
change at any time because of α-conversion.

Similarly, basic deductive steps such as ``apply`` can only operate on the
goal because the Gallina terms that control their action (e.g., the
type of the lemma used by ``apply``) only provide unnamed bound variables.
[#2]_ Since the proof script can only refer directly to the context, it
must constantly shift declarations from the goal to the context and
conversely in between deductive steps.

In |SSR|, these moves are performed by two *tacticals*, ``=>`` and
``:``, so that the bookkeeping required by a deductive step can be
directly associated with that step, and that tactics in an |SSR|
script correspond to actual logical steps in the proof rather than
merely shuffle facts. Still, some isolated bookkeeping is unavoidable,
such as naming variables and assumptions at the beginning of a
proof. |SSR| provides a specific ``move`` tactic for this purpose.

Now, ``move`` does essentially nothing: it is mostly a placeholder for
``=>`` and ``:``. The ``=>`` tactical moves variables, local definitions,
and assumptions to the context, while the ``:`` tactical moves facts and
constants to the goal.

.. example::

   For example, the proof of [#3]_

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

   .. rocqtop:: all

      Lemma subnK : forall m n, n <= m -> m - n + n = m.

   might start with

   .. rocqtop:: all

      move=> m n le_n_m.

   where ``move`` does nothing, but ``=> m n le_m_n`` changes
   the variables and assumption of the goal in the constants
   ``m n : nat`` and the fact ``le_n_m : n <= m``, thus exposing the
   conclusion ``m - n + n = m``.

   The ``:`` tactical is the converse of ``=>``; indeed it removes facts and
   constants from the context by turning them into variables and
   assumptions.

   .. rocqtop:: all

      move: m le_n_m.

   turns back ``m`` and ``le_m_n`` into a variable and an assumption,
   removing them from the proof context, and changing the goal to
   ``forall m, n <= m -> m - n + n = m``,
   which can be proved by induction on ``n`` using ``elim: n``.

Because they are tacticals, ``:`` and ``=>`` can be combined, as in

.. rocqdoc::

   move: m le_n_m => p le_n_p.

which simultaneously renames ``m`` and ``le_m_n`` into ``p`` and ``le_n_p``,
respectively, by first turning them into unnamed variables, then
turning these variables back into constants and facts.

Furthermore, |SSR| redefines the basic Rocq tactics ``case``, ``elim``,
and ``apply`` so that they can take better advantage of
``:`` and ``=>``. In these
|SSR| variants, these tactics operate on the first variable or
constant of the goal and they do not use or change the proof context.
The ``:`` tactical is used to operate on an element in the context.

.. example::

   For instance, the proof of ``subnK`` could continue with ``elim: n``.
   Instead of ``elim n`` (note, no colon), this has the advantage of
   removing n from the context. Better yet, this ``elim`` can be combined
   with previous ``move`` and with the branching version of the ``=>`` tactical
   (described in :ref:`introduction_ssr`),
   to encapsulate the inductive step in a single
   command:

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma subnK : forall m n, n <= m -> m - n + n = m.
     move=> m n le_n_m.
     elim: n m le_n_m => [|n IHn] m => [_ | lt_n_m].

  which breaks down the proof into two subgoals, the second one
  having in its context
  ``lt_n_m : S n <= m`` and
  ``IHn : forall m, n <= m -> m - n + n = m``.

The ``:`` and ``=>`` tacticals can be explained very simply if one views
the goal as a stack of variables and assumptions piled on a conclusion:

+ ``tactic : a b c`` pushes the context constants ``a``, ``b``, ``c`` as goal
  variables *before* performing the tactic;
+ ``tactic => a b c`` pops the top three goal variables as context
  constants ``a``, ``b``, ``c``, *after* the tactic has been performed.

These pushes and pops do not need to balance out as in the examples
above; so ``move: m le_n_m => p``
would rename ``m`` into ``p``, but leave an extra assumption ``n <= p``
in the goal.

Basic tactics like ``apply`` and ``elim`` can also be used without the ’:’
tactical: for example, we can directly start a proof of ``subnK`` by
induction on the top variable ``m`` with

.. rocqdoc::

   elim=> [|m IHm] n le_n.

The general form of the localization tactical ``in`` is also best
explained in terms of the goal stack::

   tactic in a H1 H2 *.

is basically equivalent to

.. rocqdoc::

   move: a H1 H2; tactic => a H1 H2.


with two differences: the ``in`` tactical will preserve the body of ``a``, if ``a``
is a defined constant, and if the ``*`` is omitted, it will use a
temporary abbreviation to hide the statement of the goal from
``tactic``.

The general form of the ``in`` tactical can be used directly with the
``move``, ``case`` and ``elim`` tactics, so that one can write

.. rocqdoc::

   elim: n => [|n IHn] in m le_n_m *.

instead of

.. rocqdoc::

   elim: n m le_n_m => [|n IHn] m le_n_m.

This is quite useful for inductive proofs that involve many facts.

See Section :ref:`localization_ssr` for
the general syntax and presentation of the ``in``
tactical.


.. _the_defective_tactics_ssr:

The defective tactics
~~~~~~~~~~~~~~~~~~~~~

In this section, we briefly present the three basic tactics performing
context manipulations and the main backward chaining tool.


The move tactic.
````````````````

.. tacn:: move
   :name: move (ssreflect)

   This tactic, in its defective form, behaves like the :tacn:`hnf` tactic.

   .. example::

      .. rocqtop:: reset all

         Require Import ssreflect.
         Goal not False.
         move.

   More precisely, the :tacn:`move <move (ssreflect)>` tactic inspects the goal and does nothing
   (:tacn:`idtac`) if an introduction step is possible, i.e., if the goal is a
   product or a ``let … in``, and performs :tacn:`hnf` otherwise.

   Of course this tactic is most often used in combination with the bookkeeping
   tacticals (see Sections :ref:`introduction_ssr` and :ref:`discharge_ssr`).
   These combinations mostly subsume the :tacn:`intros`, :tacn:`generalize`,
   :tacn:`revert`, :tacn:`rename`, :tacn:`clear` and :tacn:`pattern` tactics.


.. _the_case_tactic_ssr:

The case tactic
```````````````

.. tacn:: case
   :name: case (ssreflect)

   This tactic performs *primitive case analysis* on (co)inductive
   types; specifically, it destructs the top variable or assumption of
   the goal, exposing its constructor(s) and its arguments, as well as
   setting the value of its type family indices if it belongs to a type
   family (see Section :ref:`type_families_ssr`).

   The |SSR| ``case`` tactic has a special behavior on equalities. If the
   top assumption of the goal is an equality, the ``case`` tactic “destructs”
   it as a set of equalities between the constructor arguments of its
   left and right hand sides, as per the tactic injection. For example,
   ``case`` changes the goal::

     (x, y) = (1, 2) -> G.

   into::

     x = 1 -> y = 2 -> G.

   The :tacn:`case` can generate the following warning:

   .. warn:: SSReflect: cannot obtain new equations out of ...

      The tactic was run on an equation that cannot generate simpler equations,
      for example `x = 1`.

   The warning can be silenced or made fatal by using the :opt:`Warnings` option
   and the `spurious-ssr-injection` key.

   Finally, the :tacn:`case` tactic of |SSR| performs :g:`False` elimination, even
   if no branch is generated by this case operation. Hence the tactic
   :tacn:`case` on a goal of the form :g:`False -> G` will succeed and
   prove the goal.


The elim tactic
```````````````

.. tacn:: elim
   :name: elim (ssreflect)

   This tactic performs inductive elimination on inductive types. In its
   defective form, the tactic performs inductive elimination on a goal whose
   top assumption has an inductive type.

   .. example::

      .. rocqtop:: reset none

         From Corelib Require Import ssreflect.
         Set Implicit Arguments.
         Unset Strict Implicit.
         Unset Printing Implicit Defensive.

      .. rocqtop:: all

         Lemma test m : forall n : nat, m <= n.
         elim.


.. _apply_ssr:

The apply tactic
````````````````

.. tacn:: apply {? @term }
   :name: apply (ssreflect)

   This is the main backward chaining tactic of the proof system.
   It takes as argument any :token:`term` and applies it to the goal.
   Assumptions in the type of :token:`term` that don’t directly match the goal
   may generate one or more subgoals.

   In its defective form, this tactic is a synonym for::

     intro top; first [refine top | refine (top _) | refine (top _ _) | …]; clear top.

   where :g:`top` is a fresh name, and the sequence of :tacn:`refine` tactics
   tries to catch the appropriate number of wildcards to be inserted. Note that
   this use of the :tacn:`refine` tactic implies that the tactic tries to match
   the goal up to expansion of constants and evaluation of subterms.

:tacn:`apply <apply (ssreflect)>` has a special behavior on goals containing
existential metavariables of sort :g:`Prop`.

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.
      Axiom lt_trans : forall a b c, a < b -> b < c -> a < c.

   .. rocqtop:: all

      Lemma test : forall y, 1 < y -> y < 2 -> exists x : { n | n < 3 }, 0 < proj1_sig x.
      move=> y y_gt1 y_lt2; apply: (ex_intro _ (exist _ y _)).
        by apply: lt_trans y_lt2 _.
      by move=> y_lt3; apply: lt_trans y_gt1.

   Note that the last ``_`` of the tactic
   ``apply: (ex_intro _ (exist _ y _))``
   represents a proof that ``y < 3``. Instead of generating the goal::

      0 < proj1_sig (exist (fun n : nat => n < 3) y ?Goal).

   the system tries to prove ``y < 3`` calling the trivial tactic.
   If it succeeds, let’s say because the context contains
   ``H : y < 3``, then the
   system generates the following goal::

      0 < proj1_sig (exist (fun n => n < 3) y H).

   Otherwise the missing proof is considered to be irrelevant, and is
   thus discharged, generating the two goals shown above.

   Last, the user can replace the trivial tactic by defining an Ltac
   expression named ``ssrautoprop``.


.. _discharge_ssr:

Discharge
~~~~~~~~~

The general syntax of the discharging tactical ``:`` is:

.. tacn:: @tactic {? @ident } : {+ @d_item } {? @clear_switch }
   :name: … : … (ssreflect)
   :undocumented:

.. prodn::
   d_item ::= {? {| @occ_switch | @clear_switch } } @term
.. prodn::
   clear_switch ::= { {+ @ident } }

with the following requirements.

+ :token:`tactic` must be one of the four basic tactics described in :ref:`the_defective_tactics_ssr`,
  i.e., ``move``, ``case``, ``elim`` or ``apply``, the ``exact``
  tactic (section :ref:`terminators_ssr`),
  the ``congr`` tactic (Section :ref:`congruence_ssr`),
  or the application of the *view*
  tactical ‘/’ (Section :ref:`interpreting_assumptions_ssr`) to one of ``move``, ``case``, or ``elim``.
+ The optional :token:`ident` specifies *equation generation* (Section :ref:`generation_of_equations_ssr`),
  and is only allowed if :token:`tactic` is ``move``, ``case`` or ``elim``, or the
  application of the view tactical ‘/’ (Section :ref:`interpreting_assumptions_ssr`) to ``case`` or ``elim``.
+ An :token:`occ_switch` selects occurrences of :token:`term`, as in :ref:`abbreviations_ssr`; :token:`occ_switch`
  is not allowed if :token:`tactic` is ``apply`` or ``exact``.
+ A clear item :token:`clear_switch` specifies facts and constants to be
  deleted from the proof context (as per the ``clear`` tactic).


The ``:`` tactical first *discharges* all the :token:`d_item`, right to left,
and then performs the tactic, i.e., for each :token:`d_item`, starting with the last one :


#. The |SSR| matching algorithm described in Section :ref:`abbreviations_ssr` is
   used to find occurrences of :token:`term` in the goal, after filling any holes
   ‘_’ in the term; however if :token:`tactic` is ``apply`` or ``exact``, a different matching
   algorithm, described below, is used [#4]_.
#. These occurrences are replaced by a new variable; in particular, if
   the term is a fact, this adds an assumption to the goal.
#. If the term is *exactly* the name of a constant or fact in the proof
   context, it is deleted from the context, unless there is an
   :token:`occ_switch`.


Finally, the tactic is performed just after the first :token:`d_item`
has been generalized
— that is, between steps 2 and 3. The names listed in
the final :token:`clear_switch` (if it is present) are cleared first, before
:token:`d_item` n is discharged.

Switches affect the discharging of a :token:`d_item` as follows.


+ An :token:`occ_switch` restricts generalization (step 2) to a specific subset
  of the occurrences of the term, as per Section :ref:`abbreviations_ssr`, and prevents clearing (step
  3).
+ All the names specified by a :token:`clear_switch` are deleted from the
  context in step 3, possibly in addition to the term.


For example, the tactic:

.. rocqdoc::

   move: n {2}n (refl_equal n).

+ first generalizes ``(refl_equal n : n = n)``;
+ then generalizes the second occurrence of ``n``.
+ finally generalizes all the other occurrences of ``n``, and clears ``n``
  from the proof context (assuming ``n`` is a proof constant).

Therefore, this tactic changes any goal ``G`` into

.. rocqdoc::

   forall n n0 : nat, n = n0 -> G.

where the name ``n0`` is picked by the Rocq display function, and assuming
``n`` appeared only in ``G``.

Finally, note that a discharge operation generalizes defined constants
as variables, and not as local definitions. To override this behavior,
prefix the name of the local definition with a ``@``, like in ``move: @n``.

This is in contrast with the behavior of the ``in`` tactical (see
Section :ref:`localization_ssr`), which preserves local
definitions by default.


Clear rules
```````````

The clear step will fail if the term is a proof constant that appears in
other facts; in that case, either the facts should be cleared
explicitly with a :token:`clear_switch`, or the clear step should be disabled.
The latter can be done by adding an :token:`occ_switch` or simply by putting
parentheses around term: both
``move: (n).``
and
``move: {+}n.``
generalize ``n`` without clearing ``n`` from the proof context.

The clear step will also fail if the :token:`clear_switch` contains a :token:`ident` that
is not in the *proof* context. Note that |SSR| never clears a
section constant.

If the tactic is ``move`` or ``case`` and an equation :token:`ident` is given, then clearing
(step 3) for :token:`d_item` is suppressed (see Section :ref:`generation_of_equations_ssr`).

Intro patterns (see Section :ref:`introduction_ssr`)
and the ``rewrite`` tactic (see Section :ref:`rewriting_ssr`)
let one place a :token:`clear_switch` in the middle of other items
(namely identifiers, views and rewrite rules).  This can trigger the
addition of proof context items to the ones being explicitly
cleared, and in turn this can result in ``clear`` errors (e.g., if the
context item automatically added occurs in the goal).  The
relevant sections describe ways to avoid the unintended clearing of
context items.


Matching for apply and exact
````````````````````````````

The matching algorithm for :token:`d_item` of the |SSR|
``apply`` and ``exact``
tactics exploits the type of the first :token:`d_item` to interpret
wildcards in the
other :token:`d_item` and to determine which occurrences of these should be
generalized. Therefore, occur switches are not needed for ``apply`` and
``exact``.

Indeed, the |SSR| tactic ``apply: H x`` is equivalent to
``refine (@H _ … _ x); clear H x``,
with an appropriate number of wildcards between ``H`` and ``x``.

Note that this means that matching for ``apply`` and ``exact`` has much more
context to interpret wildcards; in particular, it can accommodate the
``_`` :token:`d_item`, which would always be rejected after ``move:``.

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.
      Axiom f : nat -> nat.
      Axiom g : nat -> nat.

   .. rocqtop:: all

      Lemma test (Hfg : forall x, f x = g x) a b : f a = g b.
      apply: trans_equal (Hfg _) _.

This tactic is equivalent (see Section
:ref:`bookkeeping_ssr`) to:
``refine (trans_equal (Hfg _) _).``
and this is a common idiom for applying transitivity on the left hand
side of an equation.


.. _abstract_ssr:

The abstract tactic
```````````````````

.. tacn:: abstract: {+ @d_item}
   :name: abstract (ssreflect)

   This tactic assigns an abstract constant previously introduced with the
   :n:`[: @ident ]` intro pattern (see Section :ref:`introduction_ssr`).

In a goal like the following::

  m : nat
  abs : <hidden>
  n : nat
  =============
  m < 5 + n

The tactic :g:`abstract: abs n` first generalizes the goal with respect to :g:`n`
(that is not visible to the abstract constant ``abs``) and then assigns
abs. The resulting goal is::

  m : nat
  n : nat
  =============
  m < 5 + n

Once this subgoal is closed, all other goals having ``abs`` in their
context see the type assigned to ``abs``. In this case::

  m : nat
  abs : forall n, m < 5 + n
  =============
  …

For a more detailed example, the reader should refer to
Section :ref:`structure_ssr`.


.. _introduction_ssr:

Introduction in the context
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The application of a tactic to a given goal can generate (quantified)
variables, assumptions, or definitions, which the user may want to
*introduce* as new facts, constants or defined constants,
respectively. If the tactic splits the goal into several subgoals,
each of them may require the introduction of different constants and
facts. Furthermore it is very common to immediately decompose or
rewrite with an assumption instead of adding it to the context, as the
goal can often be simplified and even proved after this.

All these operations are performed by the introduction tactical ``=>``,
whose general syntax is

.. tacn:: @tactic => {+ @i_item }
   :name: =>
   :undocumented:

.. prodn::
   i_item ::= {| @i_pattern | @s_item | @clear_switch | @i_view | @i_block }

.. prodn::
   s_item ::= {| /= | // | //= }

.. prodn::
   i_view ::= {? %{%} } {| /@term | /ltac:( @tactic ) }

.. prodn::
   i_pattern ::= {| @ident | > | _ | ? | * | + | {? @occ_switch } {| -> | <- } | [ {?| @i_item } ] | - | [: {+ @ident } ] }

.. prodn::
   i_block ::= {| [^ @ident ] | [^~ {| @ident | @natural } ] }

The ``=>`` tactical first executes :token:`tactic`, then the :token:`i_item`\s,
left to right. An :token:`s_item` specifies a
simplification operation; a :token:`clear_switch`
specifies context pruning as in :ref:`discharge_ssr`.
The :token:`i_pattern`\s can be seen as a variant of *intro patterns*
(see :tacn:`intros`); each performs an introduction operation, i.e., pops some
variables or assumptions from the goal.

Simplification items
`````````````````````

An :token:`s_item` can simplify the set of subgoals or the subgoals themselves.

+ ``//`` removes all the “trivial” subgoals that can be resolved by the
  |SSR| tactic :tacn:`done` described in :ref:`terminators_ssr`, i.e.,
  it executes ``try done``.
+ ``/=`` simplifies the goal by performing partial evaluation, as per the
  tactic :tacn:`simpl` [#5]_.
+ ``//=`` combines both kinds of simplification; it is equivalent to
  ``/= //``, i.e., ``simpl; try done``.


When an :token:`s_item` immediately precedes a :token:`clear_switch`, then the
:token:`clear_switch` is executed
*after* the :token:`s_item`, e.g., ``{IHn}//`` will solve some subgoals,
possibly using the fact ``IHn``, and will erase ``IHn`` from the context
of the remaining subgoals.

Views
`````

The first entry in the :token:`i_view` grammar rule, :n:`/@term`,
represents a view (see Section :ref:`views_and_reflection_ssr`).
It interprets the top of the stack with the view :token:`term`.
It is equivalent to :n:`move/@term`.

A :token:`clear_switch` that immediately precedes an :token:`i_view`
is complemented with the name of the view if an only if the :token:`i_view`
is a simple proof context entry [#10]_.
E.g., ``{}/v`` is equivalent to ``/v{v}``.
This behavior can be avoided by separating the :token:`clear_switch`
from the :token:`i_view` with the ``-`` intro pattern or by putting
parentheses around the view.

A :token:`clear_switch` that immediately precedes an :token:`i_view`
is executed after the view application.


If the next :token:`i_item` is a view, then the view is
applied to the assumption in top position once all the
previous :token:`i_item` have been performed.

The second entry in the :token:`i_view` grammar rule,
``/ltac:(`` :token:`tactic` ``)``, executes :token:`tactic`.
Notations can be used to name tactics,  for example

.. rocqtop:: none

      Tactic Notation "my" "ltac" "code" := idtac.

.. rocqtop:: in warn

   Notation "'myop'" := (ltac:(my ltac code)) : ssripat_scope.

lets one write just ``/myop`` in the intro pattern. Note the scope
annotation: views are interpreted opening the ``ssripat`` scope.  We
provide the following ltac views: ``/[dup]`` to duplicate the top of
the stack, ``/[swap]`` to swap the two first elements and ``/[apply]``
to apply the top of the stack to the next.

Intro patterns
``````````````

|SSR| supports the following :token:`i_pattern`\s.

:token:`ident`
  pops the top variable, assumption, or local definition into
  a new constant, fact, or defined constant :token:`ident`, respectively.
  Note that defined constants cannot be introduced when δ-expansion is
  required to expose the top variable or assumption.
  A :token:`clear_switch` (even an empty one) immediately preceding an
  :token:`ident` is complemented with that :token:`ident` if and only if
  the identifier is a simple proof context entry [#10]_.
  As a consequence,  by prefixing the
  :token:`ident` with ``{}`` one can *replace* a context entry.
  This behavior can be avoided by separating the :token:`clear_switch`
  from the :token:`ident` with the ``-`` intro pattern.

  Thus, trying to clear an :token:`ident` `H` with `{H}H` triggers the
  following warning:

  .. warn:: Duplicate clear of H. Use %{ %}H instead of %{ H %}H

    The warning can be silenced or made fatal with the :opt:`Warnings` option
    with the `duplicate-clear` key.

``>``
  pops every variable occurring in the rest of the stack.
  Type class instances are popped even if they don't occur
  in the rest of the stack.
  The tactic ``move=> >`` is equivalent to
  ``move=> ? ?`` on a goal such as::

    forall x y, x < y -> G

  A typical use if ``move=>> H`` to name ``H`` the first assumption,
  in the example above ``x < y``.
``?``
  pops the top variable into an anonymous constant or fact, whose name
  is picked by the tactic interpreter. |SSR| only generates names that cannot
  appear later in the user script [#6]_.
``_``
  pops the top variable into an anonymous constant that will be deleted
  from the proof context of all the subgoals produced by the ``=>`` tactical.
  They should thus never be displayed, except in an error message if the
  constant is still actually used in the goal or context after the last
  :token:`i_item` has been executed (:token:`s_item` can erase goals or
  terms where the constant appears).
``*``
  pops all the remaining apparent variables/assumptions as anonymous
  constants/facts. Unlike ``?`` and ``move``, the ``*``
  :token:`i_item` does not
  expand definitions in the goal to expose quantifiers, so it may be useful
  to repeat a ``move=> *`` tactic, e.g., on the goal::

    forall a b : bool, a <> b

  a first ``move=> *`` adds only ``_a_ : bool`` and ``_b_ : bool``
  to the context; it takes a second ``move=> *`` to add ``_Hyp_ : _a_ = _b_``.
``+``
  temporarily introduces the top variable. It is discharged at the end
  of the intro pattern. For example ``move=> + y`` on a goal::

    forall x y, P

  is equivalent to ``move=> _x_ y; move: _x_`` that results in the goal::

    forall x, P

:n:`{? occ_switch } ->`
  (resp. :token:`occ_switch` ``<-``)
  pops the top assumption (which should be a rewritable proposition) into an
  anonymous fact, rewrites (resp. rewrites right to left) the goal with this
  fact (using the |SSR| ``rewrite`` tactic described in Section
  :ref:`rewriting_ssr`, and honoring the optional occurrence selector), and
  finally deletes the anonymous fact from the context.
``[`` :token:`i_item` * ``| … |`` :token:`i_item` * ``]``
  when it is the
  very *first* :token:`i_pattern` after tactic ``=>`` tactical *and* the tactic
  is not a move, is a *branching* :token:`i_pattern`. It executes the sequence
  :n:`@i_item__i` on the i-th subgoal produced by the tactic. The
  execution of the tactic should thus generate exactly m subgoals, unless the
  ``[…]`` :token:`i_pattern` comes after an initial ``//`` or ``//=``
  :token:`s_item` that closes some of the goals produced by the tactic, in
  which case exactly m subgoals should remain after the :token:`s_item`, or we have
  the trivial branching :token:`i_pattern` [], which always does nothing,
  regardless of the number of remaining subgoals.
``[`` :token:`i_item` * ``| … |`` :token:`i_item` * ``]``
  when it is *not*
  the first :token:`i_pattern` or when the tactic is a ``move``, is a
  *destructing* :token:`i_pattern`. It starts by destructing the top
  variable, using the |SSR| ``case`` tactic described in
  :ref:`the_defective_tactics_ssr`. It then behaves as the corresponding
  branching :token:`i_pattern`, executing the
  sequence :n:`@i_item__i`  in the i-th subgoal generated by the
  case analysis; unless we have the trivial destructing :token:`i_pattern`
  ``[]``, the latter should generate exactly m subgoals, i.e., the top
  variable should have an inductive type with exactly m constructors [#7]_.
  While it is good style to use the :token:`i_item` i * to pop the variables
  and assumptions corresponding to each constructor, this is not enforced by
  |SSR|.
``-``
  does nothing, but counts as an intro pattern. It can also be used to
  force the interpretation of ``[`` :token:`i_item` * ``| … |``
  :token:`i_item` * ``]`` as a case analysis like in ``move=> -[H1 H2]``. It
  can also be used to indicate explicitly the link between a view and a name
  like in ``move=> /eqP-H1``.  Last, it can serve as a separator between
  views.  Section :ref:`views_and_reflection_ssr` [#9]_ explains in which
  respect the tactic ``move=> /v1/v2`` differs from the tactic ``move=>
  /v1-/v2``.
``[:`` :token:`ident` ``…]``
  introduces in the context an abstract constant
  for each :token:`ident`.  Its type has to be fixed later on by using the
  ``abstract`` tactic.  Before then the type displayed is ``<hidden>``.

Note that |SSR| does not support the syntax ``(ipat, …, ipat)`` for
destructing intro patterns.

Clear switch
````````````

Clears are deferred until the end of the intro pattern.

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect ssrbool.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

   .. rocqtop:: all

      Lemma test x y : Nat.leb 0 x = true -> (Nat.leb 0 x) && (Nat.leb y 2) = true.
      move=> {x} ->.

If the cleared names are reused in the same intro pattern, a renaming
is performed behind the scenes.

Facts mentioned in a clear switch must be valid names in the proof
context (excluding the section context).

Branching and destructuring
```````````````````````````

The rules for interpreting branching and destructing :token:`i_pattern` are
motivated by the fact that it would be pointless to have a branching
pattern if the tactic is a ``move``, and in most of the remaining cases
the tactic is ``case`` or ``elim``, which implies destructuring.
The rules above imply that:

+ ``move=> [a b].``
+ ``case=> [a b].``
+ ``case=> a b.``

are all equivalent, so which one to use is a matter of style; ``move`` should
be used for casual decomposition, such as splitting a pair, and ``case``
should be used for actual decompositions, in particular for type families
(see :ref:`type_families_ssr`) and proof by contradiction.

The trivial branching :token:`i_pattern` can be used to force the branching
interpretation, e.g.:

+ ``case=> [] [a b] c.``
+ ``move=> [[a b] c].``
+ ``case; case=> a b c.``

are all equivalent.

Block introduction
``````````````````

|SSR| supports the following :token:`i_block`\s.

:n:`[^ @ident ]`
  *block destructing* :token:`i_pattern`. It performs a case analysis
  on the top variable and introduces, in one go, all the variables coming
  from the case analysis. The names of these variables are obtained by
  taking the names used in the inductive type declaration and prefixing them
  with :token:`ident`. If the intro pattern immediately follows a call
  to ``elim`` with a custom eliminator (see :ref:`custom_elim_ssr`), then
  the names are taken from the ones used in the type of the eliminator.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.

     .. rocqtop:: all

        Record r := { a : nat; b := (a, 3); _ : bool; }.

        Lemma test : r -> True.
        Proof. move => [^ x ].

:n:`[^~ @ident ]`
  *block destructing* using :token:`ident` as a suffix.
:n:`[^~ @natural ]`
  *block destructing* using :token:`natural` as a suffix.

  Only a :token:`s_item` is allowed between the elimination tactic and
  the block destructing.

.. _generation_of_equations_ssr:

Generation of equations
~~~~~~~~~~~~~~~~~~~~~~~

The generation of named equations option stores the definition of a
new constant as an equation. The tactic:

.. rocqdoc::

   move En: (size l) => n.

where ``l`` is a list, replaces ``size l`` by ``n`` in the goal and
adds the fact ``En : size l = n`` to the context.
This is quite different from:

.. rocqdoc::

   pose n := (size l).

which generates a definition ``n := (size l)``. It is not possible to
generalize or rewrite such a definition; on the other hand, it is
automatically expanded during computation, whereas expanding the
equation ``En`` requires explicit rewriting.

The use of this equation name generation option with a ``case`` or an
``elim`` tactic changes the status of the first :token:`i_item`, in order to
deal with the possible parameters of the constants introduced.

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

   .. rocqtop:: all

      Lemma test (a b :nat) : a <> b.
      case E : a => [|n].

If the user does not provide a branching :token:`i_item` as first
:token:`i_item`, or if the :token:`i_item` does not provide enough names for
the arguments of a constructor, then the constants generated are introduced
under fresh |SSR| names.

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

   .. rocqtop:: all

      Lemma test (a b :nat) : a <> b.
      case E : a => H.
      Show 2.

Combining the generation of named equations mechanism with the :tacn:`case`
tactic strengthens the power of a case analysis. On the other hand,
when combined with the :tacn:`elim` tactic, this feature is mostly useful for
debug purposes, to trace the values of decomposed parameters and
pinpoint failing branches.


.. _type_families_ssr:

Type families
~~~~~~~~~~~~~

When the top assumption of a goal has an inductive type, two specific
operations are possible: the case analysis performed by the :tacn:`case`
tactic, and the application of an induction principle, performed by
the :tacn:`elim` tactic. When this top assumption has an inductive type, which
is moreover an instance of a type family, Rocq may need help from the
user to specify which occurrences of the parameters of the type should
be substituted.

.. tacv:: case: {+ @d_item } / {+ @d_item }
          elim: {+ @d_item } / {+ @d_item }

   A specific ``/`` switch indicates the type family parameters of the type
   of a :token:`d_item` immediately following this ``/`` switch.
   The :token:`d_item` on the right side of the ``/`` switch are discharged as
   described in Section :ref:`discharge_ssr`. The case analysis or elimination
   will be done on the type of the top assumption after these discharge
   operations.

   Every :token:`d_item` preceding the ``/`` is interpreted as an argument of this
   type, which should be an instance of an inductive type family. These terms
   are not actually generalized, but rather selected for substitution.
   Occurrence switches can be used to restrict the substitution. If a term is
   left completely implicit (e.g., writing just ``_``), then a pattern is
   inferred by looking at the type of the top assumption. This allows for the
   compact syntax:

   .. rocqdoc::

      case: {2}_ / eqP.

   where ``_`` is interpreted as ``(_ == _)``, since
   ``eqP T a b : reflect (a = b) (a == b)`` and ``reflect`` is a type family with
   one index.

   Moreover, if the :token:`d_item` list is too short, it is padded with an
   initial sequence of ``_`` of the right length.

   .. example::

      Here is a small example on lists. We define first a function that
      adds an element at the end of a given list.

      .. rocqtop:: reset none

         From Corelib Require Import ssreflect.
         Set Implicit Arguments.
         Unset Strict Implicit.
         Unset Printing Implicit Defensive.

      .. rocqtop:: all

         From Corelib Require Import ListDef.
         Section LastCases.
         Variable A : Type.
         Implicit Type l : list A.
         Fixpoint add_last a l : list A :=
           match l with
          | nil => a :: nil
          | hd :: tl => hd :: (add_last a tl) end.

      Then we define an inductive predicate for case analysis on lists
      according to their last element:

      .. rocqtop:: all

         Inductive last_spec : list A -> Type :=
         | LastSeq0 : last_spec nil
         | LastAdd s x : last_spec (add_last x s).

         Theorem lastP : forall l : list A, last_spec l.
         Admitted.

      We are now ready to use ``lastP`` in conjunction with ``case``.

      .. rocqtop:: all

         Lemma test l : (length l) * 2 = length (l ++ l).
         case: (lastP l).

      Applied to the same goal, the tactic ``case: l / (lastP l)``
      generates the same subgoals, but ``l`` has been cleared from both contexts:

      .. rocqtop:: all restart

         case: l / (lastP l).

      Again applied to the same goal:

      .. rocqtop:: all restart abort

         case: {1 3}l / (lastP l).

      Note that the selected occurrences on the left of the ``/``
      switch have been substituted with ``l`` instead of being affected by
      the case analysis.

   The equation name generation feature combined with a type family ``/``
   switch generates an equation for the *first* dependent :token:`d_item`
   specified by the user. Again starting with the above goal, the
   command:

   .. example::

      .. rocqtop:: all

         Lemma test l : (length l) * 2 = length (l ++ l).
         case E: {1 3}l / (lastP l) => [|s x].
         Show 2.


   There must be at least one :token:`d_item` to the left of the ``/`` switch; this
   prevents any confusion with the view feature. However, the :token:`d_item`
   to the right of the ``/`` are optional, and if they are omitted, the first
   assumption provides the instance of the type family.

   The equation always refers to the first :token:`d_item` in the actual tactic
   call, before any padding with initial ``_``. Thus, if an inductive type
   has two family parameters, it is possible to have |SSR| generate an
   equation for the second one by omitting the pattern for the first;
   note however that this will fail if the type of the second parameter
   depends on the value of the first parameter.


Control flow
------------


.. _indentation_ssr:

Indentation and bullets
~~~~~~~~~~~~~~~~~~~~~~~

A linear development of Rocq scripts gives little information on the
structure of the proof. In addition, replaying a proof after some
changes in the statement to be proved will usually not display
information to distinguish between the various branches of case
analysis for instance.

To help the user in this organization of the proof script at development
time, |SSR| provides some bullets to highlight the structure of branching
proofs. The available bullets are ``-``, ``+`` and ``*``.  Combined with
tabulation, this lets us highlight four nested levels of branching; the most
we have ever needed is three. Indeed, the use of “simpl and closing”
switches, of terminators (see Section :ref:`terminators_ssr`) and
selectors (see Section :ref:`selectors_ssr`) is powerful enough to avoid most
of the time more than two levels of indentation.

Here is a fragment of such a structured script::

    case E1: (abezoutn _ _) => [[| k1] [| k2]].
    - rewrite !muln0 !gexpn0 mulg1 => H1.
      move/eqP: (sym_equal F0); rewrite -H1 orderg1 eqn_mul1.
      by case/andP; move/eqP.
    - rewrite muln0 gexpn0 mulg1 => H1.
      have F1: t %| t * S k2.+1 - 1.
        apply: (@dvdn_trans (orderg x)); first by rewrite F0; exact: dvdn_mull.
        rewrite orderg_dvd; apply/eqP; apply: (mulgI x).
        rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
        by move: P1; case t.
      rewrite dvdn_subr in F1; last by exact: dvdn_mulr.
      + rewrite H1 F0 -{2}(muln1 (p ^ l)); congr (_ * _).
        by apply/eqP; rewrite -dvdn1.
      + by move: P1; case: (t) => [| [| s1]].
    - rewrite muln0 gexpn0 mul1g => H1.
    ...


.. _terminators_ssr:

Terminators
~~~~~~~~~~~

To further structure scripts, |SSR| supplies *terminating*
tacticals to explicitly close off tactics. When replaying scripts, we
then have the nice property that an error immediately occurs when a
closed tactic fails to prove its subgoal.

It is hence recommended practice that the proof of any subgoal should
end with a tactic that *fails if it does not solve the current goal*,
like :tacn:`discriminate`, :tacn:`contradiction` or :tacn:`assumption`.

In fact, |SSR| provides a generic tactical that turns any tactic
into a closing one (similar to :tacn:`now`). Its general syntax is:

.. tacn:: by @tactic
   :name: by
   :undocumented:

The Ltac expression :n:`by [@tactic | @tactic | …]` is equivalent to
:n:`do [done | by @tactic | by @tactic | …]`, which corresponds to the
standard Ltac expression :n:`first [done | @tactic; done | @tactic; done | …]`.

In the script provided as example in Section :ref:`indentation_ssr`, the
paragraph corresponding to each sub-case ends with a tactic line prefixed
with a ``by``, like in:

.. rocqdoc::

   by apply/eqP; rewrite -dvdn1.

.. tacn:: done
   :name: done

   The :tacn:`by` tactical is implemented using the user-defined, and extensible,
   :tacn:`done` tactic. This :tacn:`done` tactic tries to solve the current goal by some
   trivial means and fails if it doesn’t succeed. Indeed, the tactic
   expression :n:`by @tactic` is equivalent to :n:`@tactic; done`.

   Conversely, the tactic ``by [ ]`` is equivalent to :tacn:`done`.

   The default implementation of the :tacn:`done` tactic, in the ``ssreflect.v``
   file, is:

   .. rocqdoc::

      Ltac done :=
        trivial; hnf; intros; solve
         [ do ![solve [trivial | apply: sym_equal; trivial]
               | discriminate | contradiction | split]
         | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

   The iterator tactical ``do`` is presented in Section
   :ref:`iteration_ssr`. This tactic can be customized by the user,
   for instance to include an :tacn:`auto` tactic.

A natural and common way of closing a goal is to apply a lemma that
is the exact one needed for the goal to be solved. The defective form
of the tactic:

.. rocqdoc::

   exact.

is equivalent to:

.. rocqdoc::

   do [done | by move=> top; apply top].

where ``top`` is a fresh name assigned to the top assumption of the goal.
This applied form is supported by the ``:`` discharge tactical, and the
tactic:

.. rocqdoc::

   exact: MyLemma.

is equivalent to:

.. rocqdoc::

   by apply: MyLemma.

(see Section :ref:`discharge_ssr` for the documentation of the apply: combination).

.. warning::

   The list of tactics (possibly chained by semicolons) that
   follows the ``by`` keyword is considered to be a parenthesized block applied to
   the current goal. Hence for example if the tactic:

   .. rocqdoc::

      by rewrite my_lemma1.

   succeeds, then the tactic:

   .. rocqdoc::

      by rewrite my_lemma1; apply my_lemma2.

   usually fails since it is equivalent to:

   .. rocqdoc::

      by (rewrite my_lemma1; apply my_lemma2).


.. _selectors_ssr:

Selectors
~~~~~~~~~

.. tacn:: last
          first
   :name: last; first (ssreflect)

   When composing tactics, the two tacticals ``first`` and ``last`` let the user
   restrict the application of a tactic to only one of the subgoals
   generated by the previous tactic. This covers the frequent cases where
   a tactic generates two subgoals one of which can be easily disposed
   of.

   This is another powerful way of linearization of scripts, since it
   happens very often that a trivial subgoal can be solved in a less than
   one line tactic. For instance, :n:`@tactic ; last by @tactic`
   tries to solve the last subgoal generated by the first
   tactic using the given second tactic, and fails if it does not succeed.
   Its analogue :n:`@tactic ; first by @tactic`
   tries to solve the first subgoal generated by the first tactic using the
   second given tactic, and fails if it does not succeed.

|SSR| also offers an extension of this facility, by supplying
tactics to *permute* the subgoals generated by a tactic.

.. tacv:: last first
          first last
   :name: last first; first last

   These two equivalent tactics invert the order of the subgoals in focus.

   .. tacv:: last @natural first

      If :token:`natural`\'s value is :math:`k`,
      this tactic rotates the :math:`n` subgoals :math:`G_1` , …, :math:`G_n`
      in focus. Subgoal :math:`G_{n + 1 − k}` becomes the first, and the
      circular order of subgoals remains unchanged.

   .. tacn:: first @natural last
      :name: first (ssreflect)

      If :token:`natural`\'s value is :math:`k`,
      this tactic rotates the :math:`n` subgoals :math:`G_1` , …, :math:`G_n`
      in focus. Subgoal :math:`G_{k + 1 \bmod n}` becomes the first, and the circular order
      of subgoals remains unchanged.

Finally, the tactics ``last`` and ``first`` combine with the branching syntax
of Ltac: if the tactic generates n subgoals on a given goal,
then the tactic

.. rocqdoc::

   tactic ; last k [ tactic1 |…| tacticm ] || tacticn.

applies ``tactic1`` to the
:math:`n−k+1`\-th goal, … ``tacticm`` to the :math:`n−k+m`\-th goal and ``tacticn``
to the others.

.. example::

   Here is a small example on lists. We define first a function that
   adds an element at the end of a given list.

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

   .. rocqtop:: all

      Inductive test : nat -> Prop :=
      | C1 n of n = 1 : test n
      | C2 n of n = 2 : test n
      | C3 n of n = 3 : test n
      | C4 n of n = 4 : test n.

      Lemma example n (t : test n) : True.
      case: t; last 2 [move=> k| move=> l]; idtac.


.. _iteration_ssr:

Iteration
~~~~~~~~~

.. tacn:: do {? @mult } {| @tactic | [ {+| @tactic } ] }
   :name: do (ssreflect)

   This tactical offers an accurate control on the repetition of tactics.
   :token:`mult` is a *multiplier*.

   Brackets can only be omitted if a single tactic is given *and* a
   multiplier is present.

A tactic of the form:

.. rocqdoc::

   do [ tactic 1 | … | tactic n ].

is equivalent to the standard Ltac expression:

.. rocqdoc::

   first [ tactic 1 | … | tactic n ].

The optional multiplier :token:`mult` specifies how many times the action of
``tactic`` should be repeated on the current subgoal.

There are four kinds of multipliers:

.. prodn::
   mult ::= {| @natural ! | ! | @natural ? | ? }

Their meaning is as follows.

+ With ``n!``, the step tactic is repeated exactly ``n`` times (where ``n`` is a
  positive integer argument).
+ With ``!``, the step tactic is repeated as many times as possible, and done
  at least once.
+ With ``?``, the step tactic is repeated as many times as possible,
  optionally.
+ Finally, with ``n?``, the step tactic is repeated up to ``n`` times, optionally.


For instance, the tactic:

.. rocqdoc::

   tactic; do 1? rewrite mult_comm.

rewrites at most one time the lemma ``mult_comm`` in all the subgoals
generated by tactic, whereas the tactic:

.. rocqdoc::

   tactic; do 2! rewrite mult_comm.

rewrites exactly two times the lemma ``mult_comm`` in all the subgoals
generated by ``tactic``, and fails if this rewrite is not possible in some
subgoal.

Note that the combination of multipliers and rewrite is so often used
that multipliers are in fact integrated to the syntax of the
|SSR| rewrite tactic, see Section :ref:`rewriting_ssr`.


.. _localization_ssr:

Localization
~~~~~~~~~~~~

In Sections :ref:`basic_localization_ssr` and :ref:`bookkeeping_ssr`, we have
already presented the *localization* tactical ``in``, whose general syntax is:

.. tacn:: @tactic in {+ @ident} {? * }
   :name: in
   :undocumented:

where :token:`ident` is a name in the
context. On the left side of ``in``,
:token:`tactic` can be ``move``, ``case``, ``elim``, ``rewrite``, ``set``,
or any tactic formed with the general iteration tactical ``do`` (see Section
:ref:`iteration_ssr`).

The operation described by the tactic is performed in the facts listed after
``in`` and in the goal if a ``*`` ends the list of names.

The ``in`` tactical successively:

+ generalizes the selected hypotheses, possibly “protecting” the goal
  if ``*`` is not present;
+ performs :token:`tactic`, on the obtained goal;
+ reintroduces the generalized facts, under the same names.

This defective form of the ``do`` tactical is useful to avoid clashes
between standard Ltac ``in`` and the |SSR| tactical in.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Ltac mytac H := rewrite H.

     Lemma test x y (H1 : x = y) (H2 : y = 3) : x + y = 6.
     do [mytac H2] in H1 *.

  the last tactic rewrites the hypothesis ``H2 : y = 3`` both in
  ``H1 : x = y`` and in the goal ``x + y = 6``.

By default, ``in`` keeps the body of local definitions. To erase the body
of a local definition during the generalization phase, the name of the
local definition must be written between parentheses, like in
``rewrite H in H1 (def_n) H2.``

.. tacv:: @tactic in {+ {| @clear_switch | {? @}@ident | ( @ident ) | ( {? @}@ident := @c_pattern ) } } {? * }

   This is the most general form of the ``in`` tactical.
   In its simplest form, the last option lets one rename hypotheses that
   can’t be cleared (like section variables). For example, ``(y := x)``
   generalizes over ``x`` and reintroduces the generalized variable under the
   name ``y`` (and does not clear ``x``).
   For a more precise description of this form of localization, refer
   to :ref:`advanced_generalization_ssr`.


.. _structure_ssr:

Structure
~~~~~~~~~

Forward reasoning structures the script by explicitly specifying some
assumptions to be added to the proof context. It is closely associated
with the declarative style of proof, since an extensive use of these
highlighted statements makes the script closer to a (very detailed)
textbook proof.

Forward chaining tactics allow to state an intermediate lemma and start a
piece of script dedicated to the proof of this statement. The use of closing
tactics (see Section :ref:`terminators_ssr`) and of indentation makes
syntactically explicit the portion of the script building the proof of the
intermediate statement.


The have tactic.
````````````````

.. tacn:: have : @term
   :name: have

   This is the main |SSR| forward reasoning tactic. It can
   be used in two modes: one starts a new (sub)proof for an intermediate
   result in the main proof, and the other provides explicitly a proof
   term for this intermediate step.

   This tactic supports open syntax for :token:`term`. Applied to a goal ``G``, it
   generates a first subgoal requiring a proof of :token:`term` in the context of
   ``G``. The second generated subgoal is of the form :n:`term -> G`, where term
   becomes the new top assumption, instead of being introduced with a
   fresh name. At the proof-term level, the ``have`` tactic creates a β
   redex, and introduces the lemma under a fresh name, automatically
   chosen.

Like in the case of the :n:`pose (ssreflect)` tactic (see Section :ref:`definitions_ssr`), the types of
the holes are abstracted in term.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma test : True.
     have: _ * 0 = 0.

  The invocation of ``have`` is equivalent to:

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Lemma test : True.

  .. rocqtop:: all

     have: forall n : nat, n * 0 = 0.

The ``have`` tactic also enjoys the same abstraction mechanism as the :tacn:`pose (ssreflect)`
tactic for the non-inferred implicit arguments. For instance, the
tactic:

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Lemma test : True.

  .. rocqtop:: all

     have: forall x y, (x, y) = (x, y + 0).

  opens a new subgoal where the type of ``x`` is quantified.

The behavior of the defective have tactic makes it possible to
generalize it in the following general construction:

.. tacn:: have {* @i_item } {? @i_pattern } {? {| @s_item | {+ @ssr_binder } } } {? : @term } {? {| := @term | by @tactic } }
   :undocumented:

Open syntax is supported for both :token:`term`. For the description
of :token:`i_item` and :token:`s_item`, see Section
:ref:`introduction_ssr`. The first mode of the
have tactic, which opens a sub-proof for an intermediate result, uses
tactics of the form:

.. tacv:: have @clear_switch @i_item : @term by @tactic
   :undocumented:

which behaves like:

.. rocqdoc::

   have: term ; first by tactic.
   move=> clear_switch i_item.

Note that the :token:`clear_switch` *precedes* the :token:`i_item`, which
allows to reuse
a name of the context, possibly used by the proof of the assumption,
to introduce the new assumption itself.

The ``by`` feature is especially convenient when the proof script of the
statement is very short, basically when it fits in one line like in:

.. rocqdoc::

   have H23 : 3 + 2 = 2 + 3 by rewrite addnC.

The possibility of using :token:`i_item` supplies a very concise syntax for
the further use of the intermediate step. For instance,

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma test a : 3 * a - 1 = a.
     have -> : forall x, x * a = a.

  Note how the second goal was rewritten using the stated equality.
  Also note that in this last subgoal, the intermediate result does not
  appear in the context.

Thanks to the deferred execution of clears, the following idiom is
also supported (assuming x occurs in the goal only):

.. rocqdoc::

   have {x} -> : x = y.

Another frequent use of the intro patterns combined with ``have`` is the
destruction of existential assumptions like in the tactic:

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma test : True.
     have [x Px]: exists x : nat, x > 0; last first.

An alternative use of the ``have`` tactic is to provide the explicit proof
term for the intermediate lemma, using tactics of the form:

.. tacv:: have {? @ident } := @term

   This tactic creates a new assumption of type the type of :token:`term`.
   If the
   optional :token:`ident` is present, this assumption is introduced under the
   name :token:`ident`. Note that the body of the constant is lost for the user.

   Again, non-inferred implicit arguments and explicit holes are
   abstracted.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma test : True.
     have H := forall x, (x, x) = (x, x).

  adds to the context ``H : Type -> Prop.`` This is a schematic example, but
  the feature is specially useful when the proof term to give involves
  for instance a lemma with some hidden implicit arguments.

After the :token:`i_pattern`, a list of binders is allowed.

The following example requires the mathcomp and mczify libraries.

.. example::

  .. rocqtop:: reset none warn extra-mathcomp extra-mczify

     From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat zify.

     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all extra-mathcomp extra-mczify

     Lemma test : True.
     have H x (y : nat) : 2 * x + y = x + x + y by lia.

A proof term provided after ``:=`` can mention these bound variables
(that are automatically introduced with the given names).
Since the :token:`i_pattern` can be omitted, to avoid ambiguity,
bound variables can be surrounded
with parentheses even if no type is specified:

.. rocqtop:: all restart extra-mathcomp extra-mczify

   have (x) : 2 * x = x + x by lia.

The :token:`i_item` and :token:`s_item` can be used to interpret the asserted
hypothesis with views (see Section :ref:`views_and_reflection_ssr`) or simplify the resulting
goals.

The :tacn:`have` tactic also supports a ``suff`` modifier that allows for
asserting that a given statement implies the current goal without
copying the goal itself.

.. example::

  .. rocqtop:: all restart abort extra-mathcomp extra-mczify

     have suff H : 2 + 2 = 3; last first.

  Note that H is introduced in the second goal.

The ``suff`` modifier is not
compatible with the presence of a list of binders.

.. _generating_let_ssr:

Generating let in context entries with have
```````````````````````````````````````````

Since |SSR| 1.5, the :tacn:`have` tactic supports a “transparent” modifier
to generate ``let in`` context entries: the ``@`` symbol in front of the
context entry name.

.. example::

  .. rocqtop:: none

     Set Printing Depth 15.

  .. rocqtop:: all abort extra-mathcomp

     Inductive Ord n := Sub x of x < n.
     Notation "'I_ n" := (Ord n) (at level 8, n at level 2, format "''I_' n").
     Arguments Sub {_} _ _.

     Lemma test n m (H : m + 1 < n) : True.
     have @i : 'I_n by apply: (Sub m); lia.

Note that the subterm produced by :tacn:`lia` is in general huge and
uninteresting, and hence one may want to hide it.
For this purpose the ``[: name]`` intro pattern and the tactic
``abstract`` (see :ref:`abstract_ssr`) are provided.

.. example::

  .. rocqtop:: all abort extra-mathcomp

     Lemma test n m (H : m + 1 < n) : True.
     have [:pm] @i : 'I_n by apply: (Sub m); abstract: pm; lia.

  The type of ``pm`` can be cleaned up by its annotation ``(*1*)`` by just
  simplifying it. The annotations are there for technical reasons only.

When intro patterns for abstract constants are used in conjunction
with`` have`` and an explicit term, they must be used as follows:

.. example::

  .. rocqtop:: all abort extra-mathcomp

     Lemma test n m (H : m + 1 < n) : True.
     have [:pm] @i : 'I_n := Sub m pm.
       by lia.

In this case, the abstract constant ``pm`` is assigned by using it in
the term that follows ``:=`` and its corresponding goal is left to be
solved. Goals corresponding to intro patterns for abstract constants
are opened in the order in which the abstract constants are declared
(not in the “order” in which they are used in the term).

Note that abstract constants do respect scopes. Hence, if a variable
is declared after their introduction, it has to be properly
generalized (i.e., explicitly passed to the abstract constant when one
makes use of it).

.. example::

  .. rocqtop:: all abort extra-mathcomp

     Lemma test n m (H : m + 1 < n) : True.
     have [:pm] @i k : 'I_(n+k) by apply: (Sub m); abstract: pm k; lia.

Last, notice that the use of intro patterns for abstract constants is
orthogonal to the transparent flag ``@`` for ``have``.


The have tactic and typeclass resolution
```````````````````````````````````````````

Since |SSR| 1.5, the ``have`` tactic behaves as follows with respect to
typeclass inference.

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.

     Axiom ty : Type.
     Axiom t : ty.

     Goal True.

  .. rocqtop:: all

     have foo : ty.

  Full inference for ``ty``. The first subgoal demands a
  proof of such instantiated statement.

  .. A strange bug prevents using the coqtop directive here

  .. rocqdoc::

     have foo : ty := .

  No inference for ``ty``. Unresolved instances are
  quantified in ``ty``. The first subgoal demands a proof of such quantified
  statement. Note that no proof term follows ``:=``; hence two subgoals are
  generated.

  .. rocqtop:: all restart

     have foo : ty := t.

  No inference for ``ty`` and ``t``.

  .. rocqtop:: all restart abort

     have foo := t.

  No inference for ``t``. Unresolved instances are
  quantified in the (inferred) type of ``t`` and abstracted in ``t``.

.. flag:: SsrHave NoTCResolution

   This :term:`flag` restores the behavior of |SSR| 1.4 and below (never resolve typeclasses).

Variants: the suff and wlog tactics
```````````````````````````````````

As is often the case in mathematical textbooks, forward reasoning
may be used in slightly different variants. One of these variants is
to show that the intermediate step L easily implies the initial goal
G. By easily we mean here that the proof of L ⇒ G is shorter than the
one of L itself. This kind of reasoning step usually starts with: “It
suffices to show that …”.

This is such a frequent way of reasoning that |SSR| has a variant
of the ``have`` tactic called ``suffices`` (whose abridged name is ``suff``).
The
``have`` and ``suff`` tactics are equivalent and have the same syntax but:


+ the order of the generated subgoals is inverted;
+ the optional clear item is still performed in the *second*
  branch, which means that the tactic:

  .. rocqdoc::

     suff {H} H : forall x : nat, x >= 0.

  fails if the context of the current goal indeed contains an
  assumption named ``H``.


The rationale of this clearing policy is to make possible “trivial”
refinements of an assumption, without changing its name in the main
branch of the reasoning.

The ``have`` modifier can follow the ``suff`` tactic.

.. example::

  .. rocqtop:: none

     Axioms G P : Prop.

  .. rocqtop:: all abort

     Lemma test : G.
     suff have H : P.

  Note that, in contrast with ``have suff``, the name H has been introduced
  in the first goal.

Another useful construct is reduction, showing that a particular case
is in fact general enough to prove a general property. This kind of
reasoning step usually starts with: “Without loss of generality, we
can suppose that …”. Formally, this corresponds to the proof of a goal
``G`` by introducing a cut: ``wlog_statement -> G``. Hence the user shall
provide a proof for both ``(wlog_statement -> G) -> G`` and
``wlog_statement -> G``. However, such cuts are usually rather
painful to perform by
hand, because the statement ``wlog_statement`` is tedious to write by hand,
and sometimes even to read.

|SSR| implements this kind of reasoning step through the :tacn:`without loss`
tactic, whose short name is :tacn:`wlog`. It offers support to describe
the shape of the cut statements, by providing the simplifying
hypothesis and by pointing at the elements of the initial goals that
should be generalized. The general syntax of without loss is:

.. tacn:: wlog {? suff } {? @clear_switch } {? @i_item } : {* @ident } / @term
          without loss {? suff } {? @clear_switch } {? @i_item } : {* @ident } / @term
   :name: wlog; without loss
   :undocumented:

where each :token:`ident` is a constant in the context
of the goal. Open syntax is supported for :token:`term`.

In its defective form:

.. tacv:: wlog: / @term
          without loss: / @term
   :undocumented:

on a goal G, it creates two subgoals: a first one to prove the
formula (term -> G) -> G and a second one to prove the formula
term -> G.

If the optional list of :token:`ident` is present
on the left side of ``/``, these constants are generalized in the
premise (term -> G) of the first subgoal. By default bodies of local
definitions are erased. This behavior can be inhibited by prefixing the
name of the local definition with the ``@`` character.

In the second subgoal, the tactic:

.. rocqdoc::

   move=> clear_switch i_item.

is performed if at least one of these optional switches is present in
the :tacn:`wlog` tactic.

The :tacn:`wlog` tactic is specially useful when a symmetry argument
simplifies a proof. Here is an example showing the beginning of the
proof that quotient and reminder of natural number euclidean division
are unique.

The following example requires the mathcomp and mczify libraries.

.. example::

  .. rocqtop:: reset none warn extra-mathcomp

     From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

  .. rocqtop:: all extra-mathcomp

     Lemma quo_rem_unicity d q1 q2 r1 r2 :
       q1*d + r1 = q2*d + r2 -> r1 < d -> r2 < d -> (q1, r1) = (q2, r2).
     wlog: q1 q2 r1 r2 / q1 <= q2.
       by case: (leqP q1 q2); last symmetry; eauto.

The ``wlog suff`` variant is simpler, since it cuts ``wlog_statement`` instead
of ``wlog_statement -> G``. It thus opens the goals
``wlog_statement -> G``
and ``wlog_statement``.

In its simplest form, the ``generally have : …`` tactic is equivalent to
``wlog suff : …`` followed by ``last first``. When the ``have`` tactic is used
with the ``generally`` (or ``gen``) modifier, it accepts an extra identifier
followed by a comma before the usual intro pattern. The identifier
will name the new hypothesis in its more general form, while the intro
pattern will be used to process its instance.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrfun ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

     Axiom P : nat -> Prop.
     Axioms eqn leqn : nat -> nat -> bool.
     Declare Scope this_scope.
     Notation "a != b" := (eqn a b) (at level 70) : this_scope.
     Notation "a <= b" := (leqn a b) (at level 70) : this_scope.
     Open Scope this_scope.

  .. rocqtop:: all

     Lemma simple n (ngt0 : 0 < n ) : P n.
     gen have ltnV, /andP[nge0 neq0] : n ngt0 / (0 <= n) && (n != 0); last first.


.. _advanced_generalization_ssr:

Advanced generalization
+++++++++++++++++++++++

The complete syntax for the items on the left hand side of the ``/``
separator is the following one:

.. tacv:: wlog … : {? {| @clear_switch | {? @}@ident | ( {? @}@ident := @c_pattern) } } / @term
   :undocumented:

Clear operations are intertwined with generalization operations. This
helps in particular avoiding dependency issues while generalizing some
facts.

If an :token:`ident` is prefixed with the ``@`` mark, then a let-in redex is
created, which keeps track of its body (if any). The syntax
:n:`(@ident := @c_pattern)` allows to generalize an arbitrary term using a
given name. Note that its simplest form ``(x := y)`` is just a renaming of
``y`` into ``x``. In particular, this can be useful in order to simulate the
generalization of a section variable, otherwise not allowed. Indeed,
renaming does not require the original variable to be cleared.

The syntax ``(@x := y)`` generates a let-in abstraction but with the
following caveat: ``x`` will not bind ``y``, but its body, whenever ``y`` can be
unfolded. This covers the case of both local and global definitions, as
illustrated in the following example.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Section Test.
     Variable x : nat.
     Definition addx z := z + x.
     Lemma test : x <= addx x.
     wlog H : (y := x) (@twoy := addx x) / twoy = 2 * y.

  To avoid unfolding the term captured by the pattern ``add x``, one can use
  the pattern ``id (addx x)``, which would produce the following first
  subgoal

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

     Section Test.
     Variable x : nat.
     Definition addx z := z + x.
     Lemma test : x <= addx x.

  .. rocqtop:: all

     wlog H : (y := x) (@twoy := id (addx x)) / twoy = 2 * y.


.. _rewriting_ssr:

Rewriting
---------

The generalized use of reflection implies that most of the
intermediate results handled are properties of effectively computable
functions. The most efficient means of establishing such results are
computation and simplification of expressions involving such
functions, i.e., rewriting. |SSR| therefore includes an
extended ``rewrite`` tactic that unifies and combines most of the
rewriting functionalities.


An extended rewrite tactic
~~~~~~~~~~~~~~~~~~~~~~~~~~

The main features of the rewrite tactic are:

+ it can perform an entire series of such operations in any subset of
  the goal and/or context;
+ it allows to perform rewriting, simplifications, folding/unfolding
  of definitions, closing of goals;
+ several rewriting operations can be chained in a single tactic;
+ control over the occurrence at which rewriting is to be performed is
  significantly enhanced.

The general form of an |SSR| rewrite tactic is:

.. tacn:: rewrite {+ @rstep }
   :name: rewrite (ssreflect)
   :undocumented:

The combination of a rewrite tactic with the ``in`` tactical (see Section
:ref:`localization_ssr`) performs rewriting in both the context and the goal.

A rewrite step :token:`rstep` has the general form:

.. prodn::
   rstep ::= {? @r_prefix } @r_item

.. prodn::
   r_prefix ::= {? - } {? @mult } {? {| @occ_switch | @clear_switch } } {? [ @r_pattern ] }

.. prodn::
   r_pattern ::= {| @term | in {? @ident in } @term | {| @term in | @term as } @ident in @term }

.. prodn::
   r_item ::= {| {? / } @term | @s_item }

An :token:`r_prefix` contains annotations to qualify where and how the rewrite
operation should be performed.

+ The optional initial ``-`` indicates the direction of the rewriting of
  :token:`r_item`:
  if present, the direction is right-to-left and it is left-to-right otherwise.
+ The multiplier :token:`mult` (see Section :ref:`iteration_ssr`)
  specifies if and how the
  rewrite operation should be repeated.
+ A rewrite operation matches the occurrences of a *rewrite pattern*,
  and replaces these occurrences by another term, according to the
  given :token:`r_item`. The optional *redex switch* ``[r_pattern]``,
  which should
  always be surrounded by brackets, gives explicitly this rewrite
  pattern. In its simplest form, it is a regular term. If no explicit
  redex switch is present, the rewrite pattern to be matched is inferred
  from the :token:`r_item`.
+ This optional term, or the :token:`r_item`, may be preceded by an
  :token:`occ_switch` (see Section :ref:`selectors_ssr`) or a
  :token:`clear_switch` (see Section :ref:`discharge_ssr`),
  these two possibilities being exclusive.

  An occurrence switch selects
  the occurrences of the rewrite pattern that should be affected by the
  rewrite operation.

  A clear switch, even an empty one, is performed *after* the
  :token:`r_item` is actually processed and is complemented with the name of
  the rewrite rule if and only if it is a simple proof context entry [#10]_.
  As a consequence, one can
  write ``rewrite {}H`` to rewrite with ``H`` and dispose ``H`` immediately
  afterwards.
  This behavior can be avoided by putting parentheses around the rewrite rule.

A :token:`r_item` can be one of the following.


+ A *simplification* :token:`r_item`,
  represented by a :token:`s_item` (see Section
  :ref:`introduction_ssr`). Simplification operations are intertwined with the possible
  other rewrite operations specified by the list of :token:`r_item`.
+ A *folding/unfolding* :token:`r_item`. The tactic
  ``rewrite /term`` unfolds the
  :term:`head constant` of ``term`` in every occurrence of the first matching of
  ``term`` in the goal. In particular, if ``my_def`` is a (local or global)
  defined constant, the tactic ``rewrite /my_def.`` is analogous to:
  ``unfold my_def``.
  Conversely, ``rewrite -/my_def.`` is equivalent to ``fold my_def``.
  When an unfold :token:`r_item` is combined with a
  redex pattern, a conversion
  operation is performed. A tactic of the form
  ``rewrite -[term1]/term2.``
  is equivalent to ``change term1 with term2.`` If ``term2`` is a
  single constant and ``term1`` head symbol is not ``term2``, then the head
  symbol of ``term1`` is repeatedly unfolded until ``term2`` appears.
+ A :token:`term` can be:
    + a term whose type has the form:
      ``forall (x1 : A1 )…(xn : An ), eq term1 term2``, where
      ``eq`` is the Leibniz equality or a registered setoid
      equality;
    + a list of terms ``(t1 ,…,tn)``, each ``ti`` having a type as above, and
      the tactic ``rewrite r_prefix (t1 ,…,tn ).``
      is equivalent to ``do [rewrite r_prefix t1 | … | rewrite r_prefix tn ].``;
    + an anonymous rewrite lemma ``(_ : term)``, where ``term`` has a type as above.

  .. example::

     .. rocqtop:: reset none

        From Corelib Require Import ssreflect.
        Set Implicit Arguments.
        Unset Strict Implicit.
        Unset Printing Implicit Defensive.

     .. rocqtop:: all abort

        Definition double x := x + x.
        Definition ddouble x := double (double x).
        Lemma test x : ddouble x = 4 * x.
        rewrite [ddouble _]/double.

  .. warning::

     The |SSR| terms containing holes are *not* typed as
     abstractions in this context. Hence the following script fails.

     .. rocqtop:: all

        Definition f := fun x y => x + y.
        Lemma test x y : x + y = f y x.

     .. rocqtop:: all fail

        rewrite -[f y]/(y + _).

     but the following script succeeds

     .. rocqtop:: all

        rewrite -[f y x]/(y + _).


.. flag:: SsrOldRewriteGoalsOrder

   Controls the order in which generated subgoals (side conditions)
   are added to the
   proof context.  The :term:`flag` is off by default, which puts subgoals generated
   by conditional rules first, followed by the main goal.  When it is on,
   the main goal appears first.  If your proofs are organized to complete
   proving the main goal before side conditions, turning the flag on will save you
   from having to add :tacn:`last first` tactics that would be needed
   to keep the main goal as the currently focused goal.

Remarks and examples
~~~~~~~~~~~~~~~~~~~~

Rewrite redex selection
```````````````````````

The general strategy of |SSR| is to grasp as many redexes as
possible and to let the user select the ones to be rewritten thanks to
the improved syntax for the control of rewriting.

This may be a source of incompatibilities between the two rewrite
tactics.

In a rewrite tactic of the form:

.. rocqdoc::

   rewrite occ_switch [term1]term2.

``term1`` is the explicit rewrite redex and ``term2`` is the rewrite rule.
This execution of this tactic unfolds as follows.


+ First ``term1`` and ``term2`` are βι normalized. Then ``term2``
  is put in head
  normal form if the Leibniz equality constructor ``eq`` is not the head
  symbol. This may involve ζ reductions.
+ Then, the matching algorithm (see Section :ref:`abbreviations_ssr`)
  determines the
  first subterm of the goal matching the rewrite pattern. The rewrite
  pattern is given by ``term1``, if an explicit redex pattern switch is
  provided, or by the type of ``term2`` otherwise. However, matching skips
  over matches that would lead to trivial rewrites. All the occurrences
  of this subterm in the goal are candidates for rewriting.
+ Then only the occurrences coded by :token:`occ_switch` (see again Section
  :ref:`abbreviations_ssr`) are finally selected for rewriting.
+ The left-hand side of ``term2`` is unified with the subterm found by
  the matching algorithm, and if this succeeds, all the selected
  occurrences in the goal are replaced by the right-hand side of ``term2``.
+ Finally the goal is βι normalized.


In the case ``term2`` is a list of terms, the first top-down (in the
goal) left-to-right (in the list) matching rule gets selected.


Chained rewrite steps
`````````````````````

The possibility to chain rewrite operations in a single tactic makes
scripts more compact and gathers in a single command line a bunch of
surgical operations that would be described by a one sentence in a
pen and paper proof.

Performing rewrite and simplification operations in a single tactic
enhances significantly the concision of scripts. For instance the
tactic:

.. rocqdoc::

   rewrite /my_def {2}[f _]/= my_eq //=.


unfolds ``my_def`` in the goal, simplifies the second occurrence of the
first subterm matching pattern ``[f _]``, rewrites ``my_eq``, simplifies the
goals and closes trivial goals.

Here are some concrete examples of chained rewrite operations, in the
proof of basic results on natural numbers arithmetic.

.. example::


  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Axiom addn0 : forall m, m + 0 = m.
     Axiom addnS : forall m n, m + S n = S (m + n).
     Axiom addSnnS : forall m n, S m + n = m + S n.

     Lemma addnCA m n p : m + (n + p) = n + (m + p).
     by elim: m p => [ | m Hrec] p; rewrite ?addSnnS -?addnS.
     Qed.

     Lemma addnC n m : m + n = n + m.
     by rewrite -{1}[n]addn0 addnCA addn0.
     Qed.

Note the use of the ``?`` switch for parallel rewrite operations in the
proof of ``addnCA``.


Explicit redex switches are matched first
`````````````````````````````````````````

If an :token:`r_prefix` involves a *redex switch*, the first step is to find a
subterm matching this redex pattern, independently from the left-hand
side of the equality the user wants to rewrite.


.. example::


  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma test (H : forall t u, t + u = u + t) x y : x + y = y + x.
     rewrite [y + _]H.

Note that if this first pattern matching is not compatible with the
:token:`r_item`, the rewrite fails, even if the goal contains a
correct redex matching both the redex switch and the left-hand side of
the equality.

.. example::


  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma test (H : forall t u, t + u * 0 = t) x y : x + y * 4 + 2 * 0 = x + 2 * 0.
     Fail rewrite [x + _]H.

  Indeed, the left-hand side of ``H`` does not match
  the redex identified by the pattern ``x + y * 4``.

.. _ssr_rewrite_occ_switch:

Occurrence switches and redex switches
``````````````````````````````````````

.. example::


  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma test x y : x + y + 0 = x + y + y + 0 + 0 + (x + y + 0).
     rewrite {2}[_ + y + 0](_: forall z, z + 0 = z).

The second subgoal is generated by the use of an anonymous lemma in
the rewrite tactic. The effect of the tactic on the initial goal is to
rewrite this lemma at the second occurrence of the first matching
``x + y + 0`` of the explicit rewrite redex ``_ + y + 0``.

Occurrence selection and repetition
```````````````````````````````````

Occurrence selection has priority over repetition switches. This means
the repetition of a rewrite tactic specified by a multiplier will
perform matching each time an elementary rewrite operation is
performed. Repeated rewrite tactics apply to every subgoal generated
by the previous tactic, including the previous instances of the
repetition.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

  .. rocqtop:: all

     Lemma test x y (z : nat) : x + 1 = x + y + 1.
     rewrite 2!(_ : _ + 1 = z).

This last tactic generates *three* subgoals because
the second rewrite operation specified with the ``2!`` multiplier
applies to the two subgoals generated by the first rewrite.


Multi-rule rewriting
````````````````````

The rewrite tactic can be provided a *tuple* of rewrite rules, or more
generally a tree of such rules, since this tuple can feature arbitrary
inner parentheses. We call *multirule* such a generalized rewrite
rule. This feature is of special interest when it is combined with
multiplier switches, which makes the rewrite tactic iterate the
rewrite operations prescribed by the rules on the current goal.


.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

     Section Test.

  .. rocqtop:: all abort

     Variables (a b c : nat).
     Hypothesis eqab : a = b.
     Hypothesis eqac : a = c.

     Lemma test : a = a.
     rewrite (eqab, eqac).

  Indeed, rule ``eqab`` is the first to apply among the ones
  gathered in the tuple passed to the rewrite tactic. This multirule
  ``(eqab, eqac)`` is actually a Rocq term and we can name it with a
  definition:

  .. rocqtop:: all

     Definition multi1 := (eqab, eqac).

  In this case, the tactic ``rewrite multi1`` is a synonym for
  ``rewrite (eqab, eqac)``.

More precisely, a multirule rewrites the first subterm to which one of
the rules applies in a left-to-right traversal of the goal, with the
first rule from the multirule tree in left-to-right order. Matching is
performed according to the algorithm described in
Section :ref:`abbreviations_ssr`, but
literal matches have priority.

.. example::

   .. rocqtop:: all abort

      Definition d := a.
      Hypotheses eqd0 : d = 0.
      Definition multi2 := (eqab, eqd0).

      Lemma test : d = b.
      rewrite multi2.

   Indeed, rule ``eqd0`` applies without unfolding the
   definition of ``d``.

For repeated rewrites, the selection process is
repeated anew.

.. example::

  .. rocqtop:: all abort

     Hypothesis eq_adda_b : forall x, x + a = b.
     Hypothesis eq_adda_c : forall x, x + a = c.
     Hypothesis eqb0 : b = 0.
     Definition multi3 := (eq_adda_b, eq_adda_c, eqb0).

     Lemma test : 1 + a = 12 + a.
     rewrite 2!multi3.

  It uses ``eq_adda_b`` then ``eqb0`` on the left-hand
  side only. Without the bound ``2``, one would obtain ``0 = 0``.

The grouping of rules inside a multirule does not affect the selection
strategy, but can make it easier to include one rule set in another or
to (universally) quantify over the parameters of a subset of rules (as
there is special code that will omit unnecessary quantifiers for rules
that can be syntactically extracted). It is also possible to reverse
the direction of a rule subset, using a special dedicated syntax: the
tactic rewrite ``(=^~ multi1)`` is equivalent to ``rewrite multi1_rev``.

.. example::

  .. rocqtop:: all

     Hypothesis eqba : b = a.
     Hypothesis eqca : c = a.
     Definition multi1_rev := (eqba, eqca).

except that the constants ``eqba``, ``eqab`` and ``mult1_rev``
have not been created.

Rewriting with multirules is useful to implement simplification or
transformation procedures, to be applied on terms of small to medium
size. For instance, the library `ssrnat` (Mathematical Components library)
provides two implementations
for arithmetic operations on natural numbers: an elementary one and a
tail recursive version, less inefficient but also less convenient for
reasoning purposes. The library also provides one lemma per such
operation, stating that both versions return the same values when
applied to the same arguments:

.. rocqdoc::

     Lemma addE : add =2 addn.
     Lemma doubleE : double =1 doublen.
     Lemma add_mulE n m s : add_mul n m s = addn (muln n m) s.
     Lemma mulE : mul =2 muln.
     Lemma mul_expE m n p : mul_exp m n p = muln (expn m n) p.
     Lemma expE : exp =2 expn.
     Lemma oddE : odd =1 oddn.

The operation on the left-hand side of each lemma is the efficient
version, and the corresponding naive implementation is on the right-hand side. 
In order to reason conveniently on expressions involving
the efficient operations, we gather all these rules in the definition
``trecE``:

.. rocqdoc::

   Definition trecE := (addE, (doubleE, oddE), (mulE, add_mulE, (expE, mul_expE))).

The tactic ``rewrite !trecE.``
restores the naive version of each operation in a goal involving the
efficient ones, e.g., for the purpose of a correctness proof.


Wildcards vs abstractions
`````````````````````````

The rewrite tactic supports :token:`r_item`\s containing holes. For example, in
the tactic ``rewrite (_ : _ * 0 = 0).``,
the term ``_ * 0 = 0`` is interpreted as ``forall n : nat, n * 0 = 0.``
Anyway this tactic is *not* equivalent to
``rewrite (_ : forall x, x * 0 = 0).``.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

     Section Test.

  .. rocqtop:: all

     Lemma test y z : y * 0 + y * (z * 0) = 0.
     rewrite (_ : _ * 0 = 0).

  while the other tactic results in

  .. rocqtop:: all restart abort

     rewrite (_ : forall x, x * 0 = 0).

  The first tactic requires you to prove the instance of the (missing)
  lemma that was used, while the latter requires you prove the quantified
  form.

When |SSR| rewrite fails on standard Rocq licit rewrite
````````````````````````````````````````````````````````

In a few cases, the |SSR| rewrite tactic fails rewriting some
redexes that standard Rocq successfully rewrites. There are two main
cases.


+ |SSR| never accepts to rewrite indeterminate patterns like:

  .. rocqdoc::

     Lemma foo (x : unit) : x = tt.

  |SSR| will however accept the
  ηζ expansion of this rule:

  .. rocqdoc::

     Lemma fubar (x : unit) : (let u := x in u) = tt.

+ The standard rewrite tactic provided by Rocq uses a different algorithm
  to find instances of the rewrite rule.

  .. example::

    .. rocqtop:: reset none

       From Corelib Require Import ssreflect.
       Set Implicit Arguments.
       Unset Strict Implicit.
       Unset Printing Implicit Defensive.

       Section Test.

    .. rocqtop:: all

       Variable g : nat -> nat.
       Definition f := g.
       Axiom H : forall x, g x = 0.

       Lemma test : f 3 + f 3 = f 6.
       (* we call the standard rewrite tactic here *)
       rewrite -> H.

    This rewriting is not possible in |SSR|, because
    there is no occurrence of the head symbol ``f`` of the rewrite rule in the
    goal.

    .. rocqtop:: all restart fail

       rewrite H.

    Rewriting with ``H`` first requires unfolding the occurrences of
    ``f``
    where the substitution is to be performed (here there is a single such
    occurrence), using tactic ``rewrite /f`` (for a global replacement of
    ``f`` by ``g``) or ``rewrite pattern/f``, for a finer selection.

    .. rocqtop:: all restart

       rewrite /f H.

    Alternatively, one can override the pattern inferred from ``H``

    .. rocqtop:: all restart

       rewrite [f _]H.


Existential metavariables and rewriting
```````````````````````````````````````

The rewrite tactic will not instantiate existing existential
metavariables when matching a redex pattern.

If a rewrite rule generates a goal with new existential metavariables
in the ``Prop`` sort, these will be generalized as for ``apply``
(see :ref:`apply_ssr`) and
corresponding new goals will be generated.


.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrfun ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Set Warnings "-notation-overridden".

  .. rocqtop:: all abort

     Axiom leq : nat -> nat -> bool.
     Notation "m <= n" := (leq m n) : nat_scope.
     Notation "m < n"  := (S m <= n) : nat_scope.
     Inductive Ord n := Sub x of x < n.
     Notation "'I_ n" := (Ord n) (at level 8, n at level 2, format "''I_' n").
     Arguments Sub {_} _ _.
     Definition val n (i : 'I_n) := let: Sub a _ := i in a.
     Definition insub n x :=
       if @idP (x < n) is ReflectT _ Px then Some (Sub x Px) else None.
     Axiom insubT : forall n x Px, insub n x = Some (Sub x Px).

     Lemma test (x : 'I_2) y : Some x = insub 2 y.
     rewrite insubT.

  Since the argument corresponding to ``Px`` is not supplied by the user, the
  resulting goal should be ``Some x = Some (Sub y ?Goal).``
  Instead, |SSR| ``rewrite`` tactic hides the existential variable.

  As in :ref:`apply_ssr`, the ``ssrautoprop`` tactic is used to try to
  solve the existential variable.

  .. rocqtop:: all abort

     Lemma test (x : 'I_2) y (H : y < 2) : Some x = insub 2 y.
     rewrite insubT.


As a temporary limitation, this behavior is available only if the
rewriting rule is stated using Leibniz equality (as opposed to setoid
relations). It will be extended to other rewriting relations in the
future.

.. _under_ssr:

Rewriting under binders
~~~~~~~~~~~~~~~~~~~~~~~

Goals involving objects defined with higher-order functions often
require "rewriting under binders". While setoid rewriting is a
possible approach in this case, it is common to use regular rewriting
along with dedicated extensionality lemmas. This may cause some
practical issues during the development of the corresponding scripts,
notably as we might be forced to provide the rewrite tactic with
complete terms, as shown by the simple example below.

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

   .. rocqtop:: in

      Axiom subnn : forall n : nat, n - n = 0.
      Parameter map : (nat -> nat) -> list nat -> list nat.
      Parameter sumlist : list nat -> nat.
      Axiom eq_map :
        forall F1 F2 : nat -> nat,
        (forall n : nat, F1 n = F2 n) ->
        forall l : list nat, map F1 l = map F2 l.

   .. rocqtop:: all

      Lemma example_map l : sumlist (map (fun m => m - m) l) = 0.

   In this context, one cannot directly use ``eq_map``:

   .. rocqtop:: all fail

      rewrite eq_map.

   as we need to explicitly provide the non-inferable argument ``F2``,
   which corresponds here to the term we want to obtain *after* the
   rewriting step. In order to perform the rewrite step, one has to
   provide the term by hand as follows:

   .. rocqtop:: all abort

      rewrite (@eq_map _ (fun _ : nat => 0)).
        by move=> m; rewrite subnn.

   The :tacn:`under` tactic lets one perform the same operation in a more
   convenient way:

   .. rocqtop:: all abort

      Lemma example_map l : sumlist (map (fun m => m - m) l) = 0.
      under eq_map => m do rewrite subnn.


The under tactic
````````````````

The convenience :tacn:`under` tactic supports the following syntax:

.. tacn:: under {? @r_prefix } @term {? => {+ @i_item}} {? do {| @tactic | [ {*| @tactic } ] } }
   :name: under

   It operates under the context proved to be extensional by
   lemma :token:`term`.

   .. exn:: Incorrect number of tactics (expected N tactics, was given M).

      This error can occur when using the version with a ``do`` clause.

   The multiplier part of :token:`r_prefix` is not supported.

We distinguish two modes:
:ref:`interactive mode <under_interactive>`, without a ``do`` clause, and
:ref:`one-liner mode <under_one_liner>`, with a ``do`` clause,
which are explained in more detail below.

.. _under_interactive:

Interactive mode
````````````````

Let us redo the running example in interactive mode.

.. example::

   .. rocqtop:: all abort

      Lemma example_map l : sumlist (map (fun m => m - m) l) = 0.
      under eq_map => m.
        rewrite subnn.
        over.

The execution of the Ltac expression:

:n:`under @term => [ @i_item__1 | … | @i_item__n ].`

involves the following steps.

1. It performs a :n:`rewrite @term`
   without failing like in the first example with ``rewrite eq_map.``,
   but creating evars (see :tacn:`evar`). If :n:`term` is prefixed by
   a pattern or an occurrence selector, then the modifiers are honoured.

2. As an n-branch intro pattern is provided, :tacn:`under` checks that
   n+1 subgoals have been created. The last one is the main subgoal,
   while the other ones correspond to premises of the rewrite rule (such as
   ``forall n, F1 n = F2 n`` for ``eq_map``).

3. If so, :tacn:`under` puts these n goals in head normal form (using
   the defective form of the tactic :tacn:`move <move (ssreflect)>`), then executes
   the corresponding intro pattern :n:`@i_pattern__i` in each goal.

4. Then, :tacn:`under` checks that the first n subgoals
   are (quantified) Leibniz equalities, double implications or
   registered relations (w.r.t. Class ``RewriteRelation``) between a
   term and an evar, e.g., ``m - m = ?F2 m`` in the running example.
   (This support for setoid-like relations is enabled as soon as one does
   both ``Require Import ssreflect.`` and ``Require Setoid.``)

5. If so :tacn:`under` protects these n goals against an
   accidental instantiation of the evar.
   These protected goals are displayed using the ``'Under[ … ]``
   notation (e.g. ``'Under[ m - m ]`` in the running example).

6. The expression inside the ``'Under[ … ]`` notation can be
   proved equivalent to the desired expression
   by using a regular :tacn:`rewrite` tactic.

7. Interactive editing of the first n goals has to be signalled by
   using the :tacn:`over` tactic or rewrite rule (see below), which
   requires that the underlying relation is reflexive. (The running
   example deals with Leibniz equality, but ``PreOrder`` relations are
   also supported, for example.)

8. Finally, a post-processing step is performed in the main goal
   to keep the name(s) for the bound variables chosen by the user in
   the intro pattern for the first branch.

.. _over_ssr:

The over tactic
+++++++++++++++

Two equivalent facilities (a terminator and a lemma) are provided to
close intermediate subgoals generated by :tacn:`under` (i.e., goals
displayed as ``'Under[ … ]``):

.. tacn:: over
   :name: over

   This terminator tactic allows one to close goals of the form
   ``'Under[ … ]``.

.. tacv:: by rewrite over

   This is a variant of :tacn:`over` in order to close ``'Under[ … ]``
   goals, relying on the ``over`` rewrite rule.

Note that a rewrite rule ``UnderE`` is available as well, if one wants
to "unprotect" the evar, without closing the goal automatically (e.g.,
to instantiate it manually with another rule than reflexivity).

.. _under_one_liner:

One-liner mode
``````````````

The Ltac expression:

:n:`under @term => [ @i_item__1 | … | @i_item__n ] do [ @tactic__1 | … | @tactic__n ].`

can be seen as a shorter form for the following expression:

:n:`(under @term) => [ @i_item__1 | … | @i_item__n | ]; [ @tactic__1; over | … | @tactic__n; over | cbv beta iota ].`

Notes:

+ The ``beta-iota`` reduction here is useful to get rid of the beta
  redexes that could be introduced after the substitution of the evars
  by the :tacn:`under` tactic.

+ Note that the provided tactics can as well
  involve other :tacn:`under` tactics. See below for a typical example
  involving the `bigop` theory from the Mathematical Components library.

+ If there is only one tactic, the brackets can be omitted, e.g.:
  :n:`under @term => i do @tactic.` and that shorter form should be
  preferred.

+ If the ``do`` clause is provided and the intro pattern is omitted,
  then the default :token:`i_item` ``*`` is applied to each branch.
  E.g., the Ltac expression
  :n:`under @term do [ @tactic__1 | … | @tactic__n ]` is equivalent to
  :n:`under @term => [ * | … | * ] do [ @tactic__1 | … | @tactic__n ]`
  (and it can be noted here that the :tacn:`under` tactic performs a
  ``move.`` before processing the intro patterns ``=> [ * | … | * ]``).

.. example::

   .. rocqtop:: reset none

      From Corelib Require Import ssreflect.
      Set Implicit Arguments.
      Unset Strict Implicit.
      Unset Printing Implicit Defensive.

      Coercion is_true : bool >-> Sortclass.

      Reserved Notation "\big [ op / idx ]_ ( m <= i < n | P ) F"
        (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
                 format "'[' \big [ op / idx ]_ ( m  <=  i  <  n  |  P )  F ']'").
      Variant bigbody (R I : Type) : Type :=
        BigBody : forall (_ : I) (_ : forall (_ : R) (_ : R), R) (_ : bool) (_ : R), bigbody R I.

      Parameter bigop :
        forall (R I : Type) (_ : R) (_ : list I) (_ : forall _ : I, bigbody R I), R.

      Axiom eq_bigr_ :
        forall (R : Type) (idx : R) (op : forall (_ : R) (_ : R), R) (I : Type)
               (r : list I) (P : I -> bool) (F1 F2 : I -> R),
          (forall x : I, is_true (P x) -> F1 x = F2 x) ->
          bigop idx r (fun i : I => BigBody i op (P i) (F1 i)) =
          bigop idx r (fun i : I => BigBody i op (P i) (F2 i)).

      Axiom eq_big_ :
        forall (R : Type) (idx : R) (op : R -> R -> R) (I : Type) (r : list I)
               (P1 P2 : I -> bool) (F1 F2 : I -> R),
          (forall x : I, P1 x = P2 x) ->
          (forall i : I, is_true (P1 i) -> F1 i = F2 i) ->
          bigop idx r (fun i : I => BigBody i op (P1 i) (F1 i)) =
          bigop idx r (fun i : I => BigBody i op (P2 i) (F2 i)).

      Reserved Notation "\sum_ ( m <= i < n | P ) F"
        (at level 41, F at level 41, i, m, n at level 50,
                 format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").

      Parameter index_iota : nat -> nat -> list nat.

      Notation "\big [ op / idx ]_ ( m <= i < n | P ) F" :=
        (bigop idx (index_iota m n) (fun i : nat => BigBody i op P%bool F)).

      Notation "\sum_ ( m <= i < n | P ) F" :=
        (\big[plus/O]_(m <= i < n | P%bool) F%nat).

      Notation eq_bigr := (fun n m => eq_bigr_ 0 plus (index_iota n m)).
      Notation eq_big := (fun n m => eq_big_ 0 plus (index_iota n m)).

      Parameter odd : nat -> bool.
      Parameter prime : nat -> bool.

   .. rocqtop:: in

      Parameter addnC : forall m n : nat, m + n = n + m.
      Parameter muln1 : forall n : nat, n * 1 = n.

   .. rocqtop:: all

      Check eq_bigr.
      Check eq_big.

      Lemma test_big_nested (m n : nat) :
        \sum_(0 <= a < m | prime a) \sum_(0 <= j < n | odd (j * 1)) (a + j) =
        \sum_(0 <= i < m | prime i) \sum_(0 <= j < n | odd j) (j + i).
      under eq_bigr => i prime_i do
        under eq_big => [ j | j odd_j ] do
          [ rewrite (muln1 j) | rewrite (addnC i j) ].

   Remark how the final goal uses the name ``i`` (the name given in the
   intro pattern) rather than ``a`` in the binder of the first summation.

.. _locking_ssr:

Locking, unlocking
~~~~~~~~~~~~~~~~~~

As program proofs tend to generate large goals, it is important to be
able to control the partial evaluation performed by the simplification
operations that are performed by the tactics. These evaluations can,
for example, come from a ``/=`` simplification switch, or from rewrite
steps, which may expand large terms while performing conversion. We
definitely want to avoid repeating large subterms of the goal in the
proof script. We do this by “clamping down” selected function symbols
in the goal, which prevents them from being considered in
simplification or rewriting steps. This clamping is accomplished by
using the occurrence switches (see Section :ref:`abbreviations_ssr`)
together with “term tagging” operations.

|SSR| provides two levels of tagging.

The first one uses auxiliary definitions to introduce a provably equal
copy of any term ``t``. However this copy is (on purpose) *not
convertible* to ``t`` in the Rocq system [#8]_. The job is done by the
following construction:

.. rocqdoc::

   Lemma master_key : unit. Proof. exact tt. Qed.
   Definition locked A := let: tt := master_key in fun x : A => x.
   Lemma lock : forall A x, x = locked x :> A.

Note that the definition of *master_key* is explicitly opaque. The
equation ``t = locked t`` given by the ``lock`` lemma can be used for
selective rewriting, blocking on the fly the reduction in the term ``t``.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrfun ssrbool.
     From Corelib Require Import ListDef.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Variable A : Type.
     Fixpoint has (p : A -> bool) (l : list A) : bool :=
       if l is cons x l then p x || (has p l) else false.

     Lemma test p x y l (H : p x = true) : has p ( x :: y :: l) = true.
     rewrite {2}[cons]lock /= -lock.

It is sometimes desirable to globally prevent a definition from being
expanded by simplification; this is done by adding ``locked`` in the
definition.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

      Definition lid := locked (fun x : nat => x).

      Lemma test : lid 3 = 3.
      rewrite /=.
      unlock lid.

.. tacn:: unlock {? @occ_switch } @ident
   :name: unlock

   This tactic unfolds such definitions while removing “locks”; i.e., it
   replaces the occurrence(s) of :token:`ident` coded by the
   :token:`occ_switch` with the corresponding body.

We found that it was usually preferable to prevent the expansion of
some functions by the partial evaluation switch ``/=``, unless this
allowed the evaluation of a condition. This is possible thanks to another
mechanism of term tagging, resting on the following *Notation*:

.. rocqdoc::

   Notation "'nosimpl' t" := (let: tt := tt in t).

The term ``(nosimpl t)`` simplifies to ``t`` *except* in a definition.
More precisely, given:

.. rocqdoc::

   Definition foo := (nosimpl bar).

the term ``foo`` (or ``(foo t’)``) will *not* be expanded by the *simpl*
tactic unless it is in a forcing context (e.g., in ``match foo t’ with …
end``, ``foo t’`` will be reduced if this allows ``match`` to be reduced).
Note that ``nosimpl bar`` is simply notation for a term that reduces to
``bar``; hence ``unfold foo`` will replace ``foo`` by ``bar``, and
``fold foo`` will replace ``bar`` by ``foo``.

.. warning::

   The ``nosimpl`` trick only works if no reduction is apparent in
   ``t``; in particular, the declaration:

   .. rocqdoc::

      Definition foo x := nosimpl (bar x).

   will usually not work. Anyway, the common practice is to tag only the
   function, and to use the following definition, which blocks the
   reduction as expected:

   .. rocqdoc::

      Definition foo x := nosimpl bar x.

A standard example making this technique shine is the case of
arithmetic operations. We define for instance:

.. rocqdoc::

   Definition addn := nosimpl plus.

The operation ``addn`` behaves exactly like ``plus``, except that
``(addn (S n) m)`` will not simplify spontaneously to
``(S (addn n m))`` (the two terms, however, are convertible).
In addition, the unfolding step ``rewrite /addn``
will replace ``addn`` directly with ``plus``, so the ``nosimpl`` form is
essentially invisible.


.. _congruence_ssr:

Congruence
~~~~~~~~~~

Because of the way matching interferes with parameters of type families,
the tactic:

.. rocqdoc::

   apply: my_congr_property.

will generally fail to perform congruence simplification, even on
rather simple cases. We therefore provide a more robust alternative in
which the function is supplied:

.. tacn:: congr {? @natural } @term
   :name: congr

   This tactic:

   + checks that the goal is a Leibniz equality;
   + matches both sides of this equality with “term applied to some arguments”,
     inferring the right number of arguments from the goal and the type of ``term``
     (this may expand some definitions or fixpoints);
   + generates the subgoals corresponding to pairwise equalities of the arguments present in the goal.

   The goal can be a non-dependent product ``P -> Q``. In that case, the
   system asserts the equation ``P = Q``, uses it to solve the goal, and
   calls the ``congr`` tactic on the remaining goal ``P = Q``. This can be useful
   for instance to perform a transitivity step, like in the following
   situation.

   .. example::

      .. rocqtop:: reset none

         From Corelib Require Import ssreflect.
         Set Implicit Arguments.
         Unset Strict Implicit.
         Unset Printing Implicit Defensive.
         Section Test.

      .. rocqtop:: all

         Lemma test (x y z : nat) (H : x = y) : x = z.
         congr (_ = _) : H.
         Abort.

         Lemma test (x y z : nat) : x = y -> x = z.
         congr (_ = _).

   The optional :token:`natural` forces the number of arguments for which the
   tactic should generate equality proof obligations.

   This tactic supports equalities between applications with dependent
   arguments. Yet dependent arguments should have exactly the same
   parameters on both sides, and these parameters should appear as first
   arguments.

   .. example::

      .. rocqtop:: reset none

         From Corelib Require Import ssreflect.
         Set Implicit Arguments.
         Unset Strict Implicit.
         Unset Printing Implicit Defensive.
         Section Test.

      .. rocqtop:: all

         Definition f n :=
           if n is 0 then plus else mult.
         Definition g (n m : nat) := plus.

         Lemma test x y : f 0 x y = g 1 1 x y.
         congr plus.

      This script shows that the ``congr`` tactic matches ``plus``
      with ``f 0`` on the left hand side and ``g 1 1`` on the right hand
      side, and solves the goal.

   .. example::

      .. rocqtop:: reset none

         From Corelib Require Import ssreflect.
         Set Implicit Arguments.
         Unset Strict Implicit.
         Unset Printing Implicit Defensive.
         Section Test.

      .. rocqtop:: all

         Lemma test n m (Hnm : m <= n) : S m + (S n - S m) = S n.
         congr S; rewrite -/plus.

      The tactic ``rewrite -/plus`` folds back the expansion of ``plus``,
      which was necessary for matching both sides of the equality with
      an application of ``S``.

   Like most |SSR| arguments, :token:`term` can contain wildcards.

   .. example::

      .. rocqtop:: reset none

         From Corelib Require Import ssreflect.
         Set Implicit Arguments.
         Unset Strict Implicit.
         Unset Printing Implicit Defensive.
         Section Test.

      .. rocqtop:: all

         Lemma test x y : x + (y * (y + x - x)) = x * 1 + (y + 0) * y.
         congr ( _ + (_ * _)).

.. _contextual_patterns_ssr:

Contextual patterns
-------------------

The simple form of patterns used so far, terms possibly containing
wild cards, often requires an additional :token:`occ_switch` to be specified.
While this may work pretty fine for small goals, the use of
polymorphic functions and dependent types may lead to an invisible
duplication of function arguments. These copies usually end up in
types hidden by the implicit-arguments machinery or by user-defined
notations. In these situations, computing the right occurrence numbers
is very tedious, because they must be counted on the goal as printed
after setting the :flag:`Printing All` flag. Moreover, the resulting script is
not really informative for the reader, since it refers to occurrence
numbers he cannot easily see.

Contextual patterns mitigate these issues by allowing to specify
occurrences according to the context they occur in.


Syntax
~~~~~~

The following table summarizes the full syntax of :token:`c_pattern` and the
corresponding subterm(s) identified by the pattern. In the third
column, we use s.m.r. for “the subterms matching the redex” specified
in the second column.

.. list-table::
   :header-rows: 1

   * - :token:`c_pattern`
     - redex
     - subterms affected

   * - ``term``
     - ``term``
     - all occurrences of ``term``

   * - ``ident in term``
     - subterm of ``term`` selected by ``ident``
     - all the subterms identified by ``ident`` in all the
       occurrences of ``term``

   * - ``term1 in ident in term2``
     - ``term1`` in all s.m.r.
     - in all the subterms identified by
       ``ident`` in all the occurrences of ``term2``
   * - ``term1 as ident in term2``
     - ``term1``
     - in all the subterms identified by ``ident``
       in all the occurrences of ``term2[term1 /ident]``

The rewrite tactic supports two more patterns obtained prefixing the
first two with ``in``. The intended meaning is that the pattern identifies
all subterms of the specified context. The ``rewrite`` tactic will infer a
pattern for the redex looking at the rule used for rewriting.

.. list-table::
   :header-rows: 1

   * - :token:`r_pattern`
     - redex
     - subterms affected

   * - ``in term``
     - inferred from rule
     - in all s.m.r. in all occurrences of ``term``

   * - ``in ident in term``
     - inferred from rule
     - in all s.m.r. in all the subterms identified by ``ident``
       in all the occurrences of ``term``

The first :token:`c_pattern` is the simplest form matching any context but
selecting a specific redex and has been described in the previous
sections. We have seen so far that the possibility of selecting a
redex using a term with holes is already a powerful means of redex
selection. Similarly, any terms provided by the user in the more
complex forms of :token:`c_pattern`\s
presented in the tables above can contain
holes.

For a quick glance at what can be expressed with the last
:token:`r_pattern`,
consider the goal ``a = b`` and the tactic

.. rocqdoc::

   rewrite [in X in _ = X]rule.

It rewrites all occurrences of the left hand side of ``rule``
inside ``b``  only (``a``, and the hidden type of the equality, are ignored). Note that the
variant ``rewrite [X in _ = X]rule`` would have rewritten ``b``
exactly (i.e., it would only work if ``b`` and the left-hand side
of rule can be unified).


Matching contextual patterns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The :token:`c_pattern` and :token:`r_pattern` involving terms
with holes are matched
against the goal in order to find a closed instantiation. This
matching proceeds as follows:

.. list-table::
   :header-rows: 1

   * - :token:`c_pattern`
     - instantiation order and place for ``term_i`` and redex

   * - ``term``
     - ``term`` is matched against the goal, redex is unified with
       the instantiation of ``term``

   * - ``ident in term``
     - ``term`` is matched against the goal, redex is unified with the
       subterm of the instantiation of ``term`` identified by
       ``ident``

   * - ``term1 in ident in term2``
     - ``term2`` is matched against the goal, ``term1``
       is matched against the subterm of the instantiation of
       ``term1`` identified by ``ident``, redex is unified with
       the instantiation of ``term1``

   * - ``term1 as ident in term2``
     - ``term2[term1/ident]`` is matched against
       the goal, redex is unified with the instantiation of ``term1``

In the following patterns, the redex is intended to be inferred from
the rewrite rule.

.. list-table::
   :header-rows: 1

   * - :token:`r_pattern`
     - instantiation order and place for ``term_i`` and redex

   * - ``in ident in term``
     - ``term`` is matched against the goal, the redex is matched against
       the subterm of the instantiation of ``term`` identified by
       ``ident``

   * - ``in term``
     - ``term`` is matched against the goal, redex is matched against the
       instantiation of ``term``


Examples
~~~~~~~~


Contextual pattern in set and the : tactical
````````````````````````````````````````````

As already mentioned in Section :ref:`abbreviations_ssr`, the ``set``
tactic takes as an
argument a term in open syntax. This term is interpreted as the
simplest form of :token:`c_pattern`. To avoid confusion in the grammar, open
syntax is supported only for the simplest form of patterns, while
parentheses are required around more complex patterns.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Lemma test a b : a + b + 1 = b + (a + 1).
     set t := (X in _ = X).
     rewrite {}/t.
     set t := (a + _ in X in _ = X).


Since the user may define an infix notation for ``in``, the result of the former
tactic may be ambiguous. The disambiguation rule implemented is to prefer
patterns over simple terms, but to interpret a pattern with double
parentheses as a simple term. For example, the following tactic would
capture any occurrence of the term ``a in A``.

.. rocqdoc::

   set t := ((a in A)).

Contextual patterns can also be used as arguments of the ``:`` tactical.
For example:

.. rocqdoc::

   elim: n (n in _ = n) (refl_equal n).


Contextual patterns in rewrite
``````````````````````````````

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Notation "n .+1" := (Datatypes.S n) (at level 2, left associativity,
                          format "n .+1") : nat_scope.

     Axiom addSn : forall m n, m.+1 + n = (m + n).+1.
     Axiom addn0 : forall m, m + 0 = m.
     Axiom addnC : forall m n, m + n = n + m.

     Lemma test x y z f : (x.+1 + y) + f (x.+1 + y) (z + (x + y).+1) = 0.
     rewrite [in f _ _]addSn.

  Note: the simplification rule ``addSn`` is applied only under the ``f``
  symbol.
  Then, we simplify also the first addition and expand ``0`` into ``0 + 0``.

  .. rocqtop:: all

     rewrite addSn -[X in _ = X]addn0.

  Note that the right-hand side of ``addn0`` is undetermined, but the
  rewrite pattern specifies the redex explicitly. The right-hand side
  of ``addn0`` is unified with the term identified by ``X``, here ``0``.


  The following pattern does not specify a redex, since it identifies an
  entire region; hence the rewrite rule has to be instantiated
  explicitly. Thus the tactic:

  .. rocqtop:: all

     rewrite -{2}[in X in _ = X](addn0 0).

  The following tactic is quite tricky:

  .. rocqtop:: all

     rewrite [_.+1 in X in f _ X](addnC x.+1).

  The explicit redex ``_.+1`` is important, since its :term:`head constant` ``S``
  differs from the head constant inferred from
  ``(addnC x.+1)`` (that is ``+``).
  Moreover, the pattern ``f _ X`` is important to rule out
  the first occurrence of ``(x + y).+1``.
  Last, only the subterms of ``f _ X``
  identified by ``X`` are rewritten; thus the first argument of
  ``f`` is skipped too.
  Also note that the pattern ``_.+1`` is interpreted in the context
  identified by ``X``; thus it gets instantiated to
  ``(y + x).+1`` and not ``(x + y).+1``.

  The last rewrite pattern allows to specify exactly the shape of the
  term identified by X, which is thus unified with the left-hand side of
  the rewrite rule.

  .. rocqtop:: all

     rewrite [x.+1 + y as X in f X _]addnC.


Patterns for recurrent contexts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The user can define shortcuts for recurrent contexts corresponding to
the ``ident in term`` part. The notation scope identified with
``%pattern``
provides a special notation ``(X in t)`` the user must adopt
in order to define
context shortcuts.

The following example is taken from ``ssreflect.v``, where the
``LHS`` and ``RHS`` shortcuts are defined.

.. rocqdoc::

   Notation RHS := (X in _ = X)%pattern.
   Notation LHS := (X in X = _)%pattern.

Shortcuts defined this way can be freely used in place of the trailing
``ident in term`` part of any contextual pattern. Some examples follow:

.. rocqdoc::

   set rhs := RHS.
   rewrite [in RHS]rule.
   case: (a + _ in RHS).


.. _views_and_reflection_ssr:

Views and reflection
--------------------

The bookkeeping facilities presented in Section :ref:`basic_tactics_ssr` are
crafted to ease simultaneous introductions and generalizations of facts and
operations of casing, naming, etc. It is also a common practice to make a stack
operation immediately followed by an *interpretation* of the fact
being pushed, that is, to apply a lemma to this fact before passing it
to a tactic for decomposition, application and so on.

|SSR| provides a convenient, unified syntax to combine these
interpretation operations with the proof stack operations. This *view
mechanism* relies on the combination of the ``/`` view switch with
bookkeeping tactics and tacticals.

.. _custom_elim_ssr:

Interpreting eliminations
~~~~~~~~~~~~~~~~~~~~~~~~~

The view syntax combined with the ``elim`` tactic specifies an elimination
scheme to be used instead of the default, generated, one. Hence, the
|SSR| tactic:

.. rocqdoc::

   elim/V.

is a synonym for:

.. rocqdoc::

   intro top; elim top using V; clear top.

where top is a fresh name and V any second-order lemma.

Since an elimination view supports the two bookkeeping tacticals of
discharge and introduction (see Section :ref:`basic_tactics_ssr`),
the |SSR| tactic:

.. rocqdoc::

   elim/V: x => y.

is a synonym for:

.. rocqdoc::

   elim x using V; clear x; intro y.

where ``x`` is a variable in the context, ``y`` a fresh name and ``V``
any second order lemma; |SSR| relaxes the syntactic restrictions of the Rocq
``elim``. The first pattern following ``:`` can be a ``_`` wildcard if the
conclusion of the view ``V`` specifies a pattern for its last argument
(e.g., if ``V`` is a functional induction lemma generated by the
``Function`` command).

The elimination view mechanism is compatible with the equation-name
generation (see Section :ref:`generation_of_equations_ssr`).


.. example::

   The following script illustrates a toy example of this feature. Let us
   define a function adding an element at the end of a list:

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ListDef.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Variable d : Type.
     Fixpoint add_last (s : list d) (z : d) {struct s} : list d :=
       if s is cons x s' then cons x (add_last s' z) else z :: nil.

  One can define an alternative, reversed, induction principle on
  inductively defined lists, by proving the following lemma:

  .. rocqtop:: all

     Axiom last_ind_list : forall P : list d -> Prop,
       P nil -> (forall s (x : d), P s -> P (add_last s x)) ->
         forall s : list d, P s.

  Then, the combination of elimination views with equation names results
  in a concise syntax for reasoning inductively using the user-defined
  elimination scheme.

  .. rocqtop:: all

     Lemma test (x : d) (l : list d): l = l.
     elim/last_ind_list E : l=> [| u v]; last first.


User-provided eliminators (potentially generated with Coq’s ``Function``
command) can be combined with the type family switches described
in Section :ref:`type_families_ssr`.
Consider an eliminator ``foo_ind`` of type:

.. rocqdoc::

   foo_ind : forall …, forall x : T, P p1 … pm.

and consider the tactic:

.. rocqdoc::

   elim/foo_ind: e1 … / en.

The ``elim/`` tactic distinguishes two cases.

:truncated eliminator:  when ``x`` does not occur in ``P p1 … pm`` and the
  type of ``en`` unifies with ``T`` and ``en`` is not ``_``.
  In that case, ``en`` is
  passed to the eliminator as the last argument (``x`` in ``foo_ind``) and
  ``en−1 … e1`` are used as patterns to select in the goal the occurrences that
  will be bound by the predicate ``P``; thus it must be possible to unify
  the subterm of the goal matched by ``en−1`` with ``pm`` , the one matched
  by ``en−2`` with ``pm−1`` and so on.
:regular eliminator: in all the other cases. Here it must be possible
  to unify the term matched by ``en`` with ``pm`` , the one matched by
  ``en−1``
  with ``pm−1`` and so on. Note that standard eliminators have the shape
  ``…forall x, P … x``; thus ``en`` is the pattern identifying the
  eliminated term, as expected.


As explained in Section :ref:`type_families_ssr`, the initial prefix of
``ei`` can be omitted.

Here is an example of a regular, but nontrivial, eliminator.

.. example::

  Here is a toy example illustrating this feature.

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.

     Lemma plus_ind :
       forall [m : nat] [P : nat -> nat -> Prop],
       (forall n p : nat, n = S p -> P p (plus m p) -> P (S p) (S (plus m p))) ->
       (forall n _x : nat, n = _x -> match _x with
                                     | 0 => True
                                     | S _ => False
                                     end -> P _x m) -> forall n : nat, P n (plus m n).
     Admitted.

     Section Test.

  .. rocqtop:: all

     Fixpoint plus (m n : nat) {struct n} : nat :=
       if n is S p then S (plus m p) else m.

     About plus_ind.

     Lemma test x y z : plus (plus x y) z = plus x (plus y z).

  The following tactics are all valid and perform the same elimination
  on this goal.

  .. rocqdoc::

     elim/plus_ind: z / (plus _ z).
     elim/plus_ind: {z}(plus _ z).
     elim/plus_ind: {z}_.
     elim/plus_ind: z / _.

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

     Fixpoint plus (m n : nat) {struct n} : nat :=
       if n is S p then S (plus m p) else m.

     Axiom plus_ind :
       forall [m : nat] [P : nat -> nat -> Prop],
       (forall n p : nat, n = S p -> P p (plus m p) -> P (S p) (S (plus m p))) ->
       (forall n _x : nat, n = _x -> match _x with
                                     | 0 => True
                                     | S _ => False
                                     end -> P _x m) -> forall n : nat, P n (plus m n).

     Lemma test x y z : plus (plus x y) z = plus x (plus y z).

  .. rocqtop:: all

     elim/plus_ind: z / _.

  The two latter examples feature a wildcard pattern: in this case,
  the resulting pattern is inferred from the type of the eliminator.
  In both of these examples, it is ``(plus _ _)`` that matches the subterm
  ``plus (plus x y) z``, thus instantiating the last ``_`` with ``z``.
  Note that the tactic:

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

     Fixpoint plus (m n : nat) {struct n} : nat :=
       if n is S p then S (plus m p) else m.

     Axiom plus_ind :
       forall [m : nat] [P : nat -> nat -> Prop],
       (forall n p : nat, n = S p -> P p (plus m p) -> P (S p) (S (plus m p))) ->
       (forall n _x : nat, n = _x -> match _x with
                                     | 0 => True
                                     | S _ => False
                                     end -> P _x m) -> forall n : nat, P n (plus m n).

     Lemma test x y z : plus (plus x y) z = plus x (plus y z).

  .. rocqtop:: all

     Fail elim/plus_ind: y / _.

  triggers an error: in the conclusion
  of the ``plus_ind`` eliminator, the first argument of the predicate
  ``P`` should be the same as the second argument of ``plus``, in the
  second argument of ``P``, but ``y`` and ``z`` do no unify.

Here is an example of a truncated eliminator:

.. example::

  Consider the goal:

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqdoc::

     Lemma test p n (n_gt0 : 0 < n) (pr_p : prime p) :
       p %| \prod_(i <- prime_decomp n | i \in prime_decomp n) i.1 ^ i.2 ->
         exists2 x : nat * nat, x \in prime_decomp n & p = x.1.
     Proof.
     elim/big_prop: _ => [| u v IHu IHv | [q e] /=].


  where the type of the ``big_prop`` eliminator is

  .. rocqdoc::

     big_prop: forall (R : Type) (Pb : R -> Type)
       (idx : R) (op1 : R -> R -> R), Pb idx ->
       (forall x y : R, Pb x -> Pb y -> Pb (op1 x y)) ->
       forall (I : Type) (r : seq I) (P : pred I) (F : I -> R),
       (forall i : I, P i -> Pb (F i)) ->
         Pb (\big[op1/idx]_(i <- r | P i) F i).

  Since the pattern for the argument of Pb is not specified, the
  inferred one, ``big[_/_]_(i <- _ | _ i) _ i``, is used instead,
  and after the introductions, the following goals are generated:

  .. rocqdoc::

     subgoal 1 is:
       p %| 1 -> exists2 x : nat * nat, x \in prime_decomp n & p = x.1
     subgoal 2 is:
       p %| u * v -> exists2 x : nat * nat, x \in prime_decomp n & p = x.1
     subgoal 3 is:
       (q, e) \in prime_decomp n -> p %| q ^ e ->
         exists2 x : nat * nat, x \in prime_decomp n & p = x.1.

  Note that the pattern matching algorithm instantiated all the
  variables occurring in the pattern.


.. _interpreting_assumptions_ssr:

Interpreting assumptions
~~~~~~~~~~~~~~~~~~~~~~~~

Interpreting an assumption in the context of a proof consists in
applying to it a lemma before generalizing and/or decomposing this
assumption. For instance, with the extensive use of boolean reflection
(see Section :ref:`views_and_reflection_ssr`), it is quite frequent
to need to decompose the logical interpretation of (the boolean
expression of) a fact, rather than the fact itself. This can be
achieved by a combination of ``move : _ => _`` switches, like in the
following example, where ``||`` is a notation for the boolean
disjunction.


.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Variables P Q : bool -> Prop.
     Hypothesis P2Q : forall a b, P (a || b) -> Q a.

     Lemma test a : P (a || a) -> True.
     move=> HPa; move: {HPa}(P2Q HPa) => HQa.

  which transforms the hypothesis ``HPa : P a``, which has been introduced
  from the initial statement, into ``HQa : Q a``.
  This operation is so common that the tactic shell has specific
  syntax for it. The following scripts:

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

     Variables P Q : bool -> Prop.
     Hypothesis P2Q : forall a b, P (a || b) -> Q a.

     Lemma test a : P (a || a) -> True.

  .. rocqtop:: all

     move=> HPa; move/P2Q: HPa => HQa.

  or more directly:

  .. rocqtop:: all restart

     move/P2Q=> HQa.

  are equivalent to the former one. The former script shows how to
  interpret a fact (already in the context), thanks to the discharge
  tactical (see Section :ref:`discharge_ssr`), and the latter, how to interpret the top
  assumption of a goal. Note that the number of wildcards to be inserted
  to find the correct application of the view lemma to the hypothesis
  has been automatically inferred.

The view mechanism is compatible with the ``case`` tactic and with the
equation-name generation mechanism (see Section :ref:`generation_of_equations_ssr`):

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Variables P Q: bool -> Prop.
     Hypothesis Q2P : forall a b, Q (a || b) -> P a \/ P b.

     Lemma test a b : Q (a || b) -> True.
     case/Q2P=> [HPa | HPb].

  This view tactic performs:

  .. rocqdoc::

     move=> HQ; case: {HQ}(Q2P HQ) => [HPa | HPb].

The term on the right of the ``/`` view switch is called a *view lemma*.
Any |SSR| term coercing to a product type can be used as a view
lemma.

The examples we have given so far explicitly provide the direction of
the translation to be performed. In fact, view lemmas need not to be
oriented. The view mechanism is able to detect which application is
relevant for the current goal.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Variables P Q: bool -> Prop.
     Hypothesis PQequiv : forall a b, P (a || b) <-> Q a.

     Lemma test a b : P (a || b) -> True.
     move/PQequiv=> HQab.

  has the same behavior as the first example above.

  The view mechanism can insert automatically a *view hint* to transform
  the double implication into the expected simple implication. The last
  script is in fact equivalent to:

  .. rocqdoc::

     Lemma test a b : P (a || b) -> True.
     move/(iffLR (PQequiv _ _)).

  where:

  .. rocqdoc::

     Lemma iffLR P Q : (P <-> Q) -> P -> Q.


Specializing assumptions
````````````````````````

The special case when the *head symbol* of the view lemma is a
wildcard is used to interpret an assumption by *specializing* it. The
view mechanism hence offers the possibility to apply a higher-order
assumption to some given arguments.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Lemma test z : (forall x y, x + y = z -> z = x) -> z = 0.
     move/(_ 0 z).


Interpreting goals
~~~~~~~~~~~~~~~~~~

In a similar way, it is also often convenient to
change a goal by turning it into an equivalent proposition. The view
mechanism of |SSR| has a special syntax ``apply/`` for combining  in a
single tactic simultaneous goal interpretation operations and
bookkeeping steps.


.. example::

   The following example use the ``~~`` prenex notation for boolean negation:


  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Variables P Q: bool -> Prop.
     Hypothesis PQequiv : forall a b, P (a || b) <-> Q a.

     Lemma test a : P ((~~ a) || a).
     apply/PQequiv.

  thus in this case, the tactic ``apply/PQequiv`` is equivalent to
  ``apply: (iffRL (PQequiv _ _))``, where ``iffRL`` is the analogue of
  ``iffLR`` for the converse implication.

Any |SSR| term whose type coerces to a double implication can be
used as a view for goal interpretation.

Note that the goal interpretation view mechanism supports both ``apply``
and ``exact`` tactics. As expected, a goal interpretation view command
``exact``/term should solve the current goal or it will fail.

.. warning::

   Goal-interpretation view tactics are *not* compatible with
   the bookkeeping tactical ``=>``, since this would be redundant with the
   ``apply: term => _`` construction.


Boolean reflection
~~~~~~~~~~~~~~~~~~

In the Calculus of Inductive Constructions, there is an obvious
distinction between logical propositions and boolean values. On the
one hand, logical propositions are objects of *sort* ``Prop``, which is
the carrier of intuitionistic reasoning. Logical connectives in
``Prop`` are *types*, which give precise information on the structure
of their proofs; this information is automatically exploited by Rocq
tactics.  For example, Rocq knows that a proof of ``A \/ B`` is
either a proof of ``A`` or a proof of ``B``.  The tactics ``left`` and
``right`` change the goal ``A \/ B`` to ``A`` and ``B``, respectively;
dually, the tactic ``case`` reduces the goal ``A \/ B => G`` to two
subgoals ``A => G`` and ``B => G``.

On the other hand, bool is an inductive *datatype* with two
constructors: ``true`` and ``false``. Logical connectives on bool are
*computable functions*, defined by their truth tables, using case
analysis:

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Definition orb (b1 b2 : bool) := if b1 then true else b2.

Properties of such connectives are also established using case
analysis

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Lemma test b : b || ~~ b = true.
     by case: b.

  Once ``b`` is replaced by ``true`` in the first goal and by ``false`` in the
  second one, the goals reduce by computation to the trivial ``true = true``.

Thus, ``Prop`` and ``bool`` are truly complementary: the former supports
robust natural deduction; the latter allows brute-force
evaluation. |SSR| supplies a generic mechanism to have the best of
the two worlds and move freely from a propositional version of a
decidable predicate to its boolean version.

First, booleans are injected into propositions using the coercion
mechanism:

.. rocqdoc::

   Coercion is_true (b : bool) := b = true.

This allows any boolean formula ``b`` to be used in a context where Rocq
would expect a proposition, e.g., after ``Lemma … :``. It is then
interpreted as ``(is_true b)``, i.e., the proposition ``b = true``. Coercions
are elided by the pretty-printer; so they are essentially transparent
to the user.

The reflect predicate
~~~~~~~~~~~~~~~~~~~~~

To get all the benefits of the boolean reflection, it is in fact
convenient to introduce the following inductive predicate ``reflect`` to
relate propositions and booleans:

.. rocqdoc::

   Inductive reflect (P: Prop): bool -> Type :=
   | Reflect_true : P -> reflect P true
   | Reflect_false : ~P -> reflect P false.

The statement ``(reflect P b)`` asserts that ``(is_true b)`` and ``P`` are
logically equivalent propositions.

For instance, the following lemma:

.. rocqdoc::

   Lemma andP: forall b1 b2, reflect (b1 /\ b2) (b1 && b2).

relates the boolean conjunction to the logical one ``/\``. Note that in
``andP``, ``b1`` and ``b2`` are two boolean variables and the
proposition ``b1 /\ b2`` hides two coercions. The conjunction of
``b1`` and ``b2`` can then be viewed as ``b1 /\ b2`` or as ``b1 && b2``.

Expressing logical equivalences through this family of inductive types
makes possible to take benefit from *rewritable equations* associated
to the case analysis of Rocq's inductive types.

Since the equivalence predicate is defined in Rocq as:

.. rocqdoc::

   Definition iff (A B:Prop) := (A -> B) /\ (B -> A).

where ``/\`` is a notation for ``and``:

.. rocqdoc::

   Inductive and (A B:Prop) : Prop := conj : A -> B -> and A B.

This makes case analysis very different according to the way an
equivalence property has been defined.

.. rocqdoc::

   Lemma andE (b1 b2 : bool) : (b1 /\ b2) <-> (b1 && b2).

Let us compare the respective behaviors of ``andE`` and ``andP``.


.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.
     Axiom andE : forall (b1 b2 : bool), (b1 /\ b2) <-> (b1 && b2).

  .. rocqtop:: all

     Lemma test (b1 b2 : bool) : if (b1 && b2) then b1 else ~~(b1||b2).

  .. rocqtop:: all

     case: (@andE b1 b2).

  .. rocqtop:: none

     Restart.

  .. rocqtop:: all

     case: (@andP b1 b2).

Expressing reflection relations through the ``reflect`` predicate is hence
a very convenient way to deal with classical reasoning, by case
analysis. Using the ``reflect`` predicate allows, moreover, to program rich
specifications inside its two constructors, which will be
automatically taken into account during destruction. This
formalisation style gives far more efficient specifications than
quantified (double) implications.

A naming convention in |SSR| is to postfix the name of view lemmas
with ``P``. For example, ``orP`` relates ``||`` and ``\/``;
``negP`` relates ``~~`` and ``~``.

The view mechanism is compatible with reflect predicates.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all abort

     Lemma test (a b : bool) (Ha : a) (Hb : b) : a /\ b.
     apply/andP.

  Conversely

  .. rocqtop:: all

     Lemma test (a b : bool) : a /\ b -> a.
     move/andP.

The same tactics can also be used to perform the converse operation,
changing a boolean conjunction into a logical one. The view mechanism
guesses the direction of the transformation to be used, i.e., the
constructor of the reflect predicate that should be chosen.


General mechanism for interpreting goals and assumptions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Specializing assumptions
````````````````````````

The |SSR| tactic:

.. rocqdoc::

   move/(_ term1 … termn).

is equivalent to the tactic:

.. rocqdoc::

   intro top; generalize (top term1 … termn); clear top.

where ``top`` is a fresh name for introducing the top assumption of the
current goal.


Interpreting assumptions
````````````````````````

The general form of an assumption view tactic is:

.. tacv:: {| move | case } / @term
   :undocumented:

The term, called the *view lemma*, can be:


+ a (term coercible to a) function;
+ a (possibly quantified) implication;
+ a (possibly quantified) double implication;
+ a (possibly quantified) instance of the reflect predicate (see
  Section :ref:`views_and_reflection_ssr`).


Let ``top`` be the top assumption in the goal.

There are three steps in the behavior of an assumption view tactic.

+ It first introduces ``top``.
+ If the type of :token:`term` is neither a double implication nor an
  instance of the reflect predicate, then the tactic automatically
  generalises a term of the form ``term term1 … termn``, where the
  terms ``term1 … termn`` instantiate the possible quantified variables of
  ``term`` , in order for ``(term term1 … termn top)`` to be well typed.
+ If the type of ``term`` is an equivalence, or an instance of the
  reflect predicate, it generalises a term of the form
  ``(termvh (term term1 … termn ))``, where the term ``termvh``
  inserted is called an
  *assumption interpretation view hint*.
+ It finally clears top.


For a ``case/term`` tactic, the generalisation step is replaced by a
case analysis step.

*View hints* are declared by the user (see Section :ref:`views_and_reflection_ssr`) and
stored in the Hint View database. The proof engine automatically
detects from the shape of the top assumption ``top`` and of the view lemma
``term`` provided to the tactic the appropriate view hint in the
database to be inserted.

If ``term`` is a double implication, then the view hint will be one of
the defined view hints for implication. These hints are by default the
ones present in the file ``ssreflect.v``:

.. rocqdoc::

   Lemma iffLR : forall P Q, (P <-> Q) -> P -> Q.

which transforms a double implication into the left-to-right one, or:

.. rocqdoc::

   Lemma iffRL : forall P Q, (P <-> Q) -> Q -> P.

which produces the converse implication. In both cases, the two
first ``Prop`` arguments are implicit.

If ``term`` is an instance of the ``reflect`` predicate, then ``A`` will be one
of the defined view hints for the ``reflect`` predicate, which are by
default the ones present in the file ``ssrbool.v``. These hints are not
only used for choosing the appropriate direction of the translation,
but they also allow complex transformation, involving negations.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Check introN.

  .. rocqtop:: all

     Lemma test (a b : bool) (Ha : a) (Hb : b) : ~~ (a && b).
     apply/andP.

  In fact, this last script does not
  exactly use the hint ``introN``, but the more general hint:

  .. rocqtop:: all

     Check introNTF.

  The lemma ``introN`` is an instantiation of ``introNF`` using ``c := true``.

Note that views, being part of :token:`i_pattern`, can be used to interpret
assertions too. For example, the following script asserts ``a && b``, but
actually uses its propositional interpretation.


.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Lemma test (a b : bool) (pab : b && a) : b.
     have /andP [pa ->] : (a && b) by rewrite andbC.

Interpreting goals
``````````````````

A goal interpretation view tactic of the form:

.. tacv:: apply/@term
   :undocumented:

applied to a goal ``top`` is interpreted in the following way.

+ If the type of ``term`` is not an instance of the reflect predicate,
  nor an equivalence, then the term ``term`` is applied to the current
  goal ``top``, possibly inserting implicit arguments.
+ If the type of ``term`` is an instance of the reflect predicate or an
  equivalence, then a *goal interpretation view hint* can possibly be
  inserted, which corresponds to the application of a term
  ``(termvh (term _ … _))`` to the current goal, possibly inserting implicit arguments.


Like assumption interpretation view hints, goal interpretation ones
are user-defined lemmas stored (see Section :ref:`views_and_reflection_ssr`) in the ``Hint View``
database, bridging the possible gap between the type of ``term`` and the
type of the goal.


Interpreting equivalences
~~~~~~~~~~~~~~~~~~~~~~~~~

Equivalent boolean propositions are simply *equal* boolean terms. A
special construction helps the user to prove boolean equalities by
considering them as logical double implications (between their coerced
versions), while performing at the same time logical operations on
both sides.

The syntax of double views is:

.. tacv:: apply/@term/@term
   :undocumented:

The first term is the view lemma applied to the left-hand side of the
equality, while the second term is the one applied to the right-hand side.

In this context, the identity view can be used when no view has to be applied:

.. rocqdoc::

   Lemma idP : reflect b1 b1.

.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Lemma test (b1 b2 b3 : bool) : ~~ (b1 || b2) = b3.
     apply/idP/idP.

  The same goal can be decomposed in several ways, and the user may
  choose the most convenient interpretation.

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.

  .. rocqtop:: all

     Lemma test (b1 b2 b3 : bool) : ~~ (b1 || b2) = b3.
     apply/norP/idP.


.. _declaring_new_hints_ssr:

Declaring new Hint Views
~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Hint View for move / @ident {? | @natural }
         Hint View for apply / @ident {? | @natural }

   This command can be used to extend the database of hints for the view
   mechanism.

   As library ``ssrbool.v`` already declares a
   corpus of hints, this feature is probably useful only for users who
   define their own logical connectives.

   The :token:`ident` is the name of the lemma to be
   declared as a hint. If ``move`` is used as
   tactic, the hint is declared for assumption interpretation tactics;
   ``apply`` declares hints for goal interpretations. Goal interpretation
   view hints are declared for both simple views and left-hand side
   views. The optional natural number is the number of implicit
   arguments to be considered for the declared hint view lemma.

   .. cmdv:: Hint View for apply//@ident {? | @natural }

      This variant with a double slash ``//`` declares hint views for 
      right-hand sides of double views.

      See the files ``ssreflect.v`` and ``ssrbool.v`` for examples.


Multiple views
~~~~~~~~~~~~~~

The hypotheses and the goal can be interpreted by applying multiple views
in sequence. Both ``move`` and ``apply`` can be followed by an arbitrary
number of ``/term``. The main difference between the following two
tactics

.. rocqdoc::

   apply/v1/v2/v3.
   apply/v1; apply/v2; apply/v3.

is that the former applies all the views to the principal goal.
Applying a view with hypotheses generates new goals, and the second
line would apply the view ``v2`` to all the goals generated by ``apply/v1``.

Note that the NO-OP intro pattern ``-`` can be used to separate two views,
making the two following examples equivalent:

.. rocqdoc::

   move=> /v1; move=> /v2.
   move=> /v1 - /v2.

The tactic ``move`` can be used together with the ``in`` tactical to
pass a given hypothesis to a lemma.


.. example::

  .. rocqtop:: reset none

     From Corelib Require Import ssreflect ssrbool.
     Set Implicit Arguments.
     Unset Strict Implicit.
     Unset Printing Implicit Defensive.
     Section Test.
     Variables P Q R : Prop.

  .. rocqtop:: all

     Variable P2Q : P -> Q.
     Variable Q2R : Q -> R.

     Lemma test (p : P) : True.
     move/P2Q/Q2R in p.

If the list of views is of length two, ``Hint Views`` for interpreting
equivalences are indeed taken into account; otherwise only single
``Hint Views`` are used.


Additional view shortcuts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following intro pattern ltac views are provided:

+ ``/[apply]`` shortcut for ``=> hyp {}/hyp``
+ ``/[swap]`` shortcut for ``=> x y; move: y x`` which swaps and preserves let
  bindings
+ ``/[dup]`` shortcut for ``=> x; have copy := x; move: copy x`` which
  copies and preserves let bindings

One can call rewrite from an intro pattern, use with parsimony:

+ ``/[1! rules]`` shortcut for ``rewrite rules``
+ ``/[! rules]`` shortcut for ``rewrite !rules``


Synopsis and Index
------------------

Parameters
~~~~~~~~~~

|SSR| tactics

.. prodn::
   d_tactic ::= {| elim | case | congr | apply | exact | move }

Notation scope

.. prodn:: key ::= @ident

Module name

.. prodn:: modname ::= @qualid

Natural number

.. prodn:: nat_or_ident ::= {| @natural | @ident }

where :token:`ident` is an Ltac variable denoting a standard Rocq number
(should not be the name of a tactic that can be followed by a
bracket ``[``, such as ``do``, ``have``,…)

Items and switches
~~~~~~~~~~~~~~~~~~

.. prodn:: ssr_binder ::= {| @ident | ( @ident {? : @term } ) }

binder (see :ref:`abbreviations_ssr`)

.. prodn:: clear_switch ::= { {+ @ident } }

clear switch (see :ref:`discharge_ssr`)

.. prodn:: c_pattern ::= {? {| @term in | @term as } } @ident in @term

context pattern (see :ref:`contextual_patterns_ssr`)

.. prodn:: d_item ::= {? {| @occ_switch | @clear_switch } } {? {| @term | ( @c_pattern ) } }

discharge item (see :ref:`discharge_ssr`)

.. prodn:: gen_item ::= {| {? @ } @ident | ( @ident ) | ( {? @ } @ident := @c_pattern ) }

generalization item (see :ref:`structure_ssr`)

.. prodn:: i_pattern ::= {| @ident | > | _ | ? | * | + | {? @occ_switch } {| -> | <- } | [ {?| @i_item } ] | - | [: {+ @ident } ] }

intro pattern (see :ref:`introduction_ssr`)

.. prodn:: i_item ::= {| @clear_switch | @s_item | @i_pattern | @i_view | @i_block }

view (see :ref:`introduction_ssr`)

.. prodn::
   i_view ::= {? %{%} } {| /@term | /ltac:( @tactic ) }

intro block (see :ref:`introduction_ssr`)

.. prodn::
   i_block ::= {| [^ @ident ] | [^~ {| @ident | @natural } ] }

intro item (see :ref:`introduction_ssr`)

.. prodn:: int_mult ::= {? @natural } @mult_mark

multiplier (see :ref:`iteration_ssr`)

.. prodn:: occ_switch ::= { {? {| + | - } } {* @natural } }

occur. switch (see :ref:`occurrence_selection_ssr`)

.. prodn:: mult ::= {? @natural } @mult_mark

multiplier (see :ref:`iteration_ssr`)

.. prodn:: mult_mark ::= {| ? | ! }

multiplier mark (see :ref:`iteration_ssr`)

.. prodn:: r_item ::= {| {? / } @term | @s_item }

rewrite item (see :ref:`rewriting_ssr`)

.. prodn:: r_prefix ::= {? - } {? @int_mult } {? {| @occ_switch | @clear_switch } } {? [ @r_pattern ] }

rewrite prefix (see :ref:`rewriting_ssr`)

.. prodn:: r_pattern ::= {| @term | @c_pattern | in {? @ident in } @term }

rewrite pattern (see :ref:`rewriting_ssr`)

.. prodn:: r_step ::= {? @r_prefix } @r_item

rewrite step (see :ref:`rewriting_ssr`)

.. prodn:: s_item ::= {| /= | // | //= }

simplify switch (see :ref:`introduction_ssr`)

Tactics
~~~~~~~

*Note*: ``without loss`` and ``suffices`` are synonyms for ``wlog`` and ``suff``,
respectively.

.. tacn:: move
   :name: move (ssreflect)

   :tacn:`idtac` or :tacn:`hnf` (see  :ref:`bookkeeping_ssr`)

.. tacn:: apply
          exact
   :name: apply (ssreflect); exact (ssreflect)

   application (see :ref:`the_defective_tactics_ssr`)

.. tacv:: abstract: {+ @d_item}

   (see :ref:`abstract_ssr` and :ref:`generating_let_ssr`)

.. tacv:: elim

   induction (see :ref:`the_defective_tactics_ssr`)

.. tacv:: case

   case analysis (see :ref:`the_defective_tactics_ssr`)

.. tacv:: rewrite {+ @r_step }

   rewrite (see :ref:`rewriting_ssr`)

.. tacn:: under {? @r_prefix } @term {? => {+ @i_item}} {? do {| @tactic | [ {*| @tactic } ] } }

   under (see :ref:`under_ssr`)

.. tacn:: over

   over (see :ref:`over_ssr`)

.. tacn:: have {* @i_item } {? @i_pattern } {? {| @s_item | {+ @ssr_binder } } } {? : @term } := @term
          have {* @i_item } {? @i_pattern } {? {| @s_item | {+ @ssr_binder } } } : @term {? by @tactic }
          have suff {? @clear_switch } {? @i_pattern } {? : @term } := @term
          have suff {? @clear_switch } {? @i_pattern } : @term {? by @tactic }
          gen have {? @ident , } {? @i_pattern } : {+ @gen_item } / @term {? by @tactic }
          generally have {? @ident , } {? @i_pattern } : {+ @gen_item } / @term {? by @tactic }
   :name: _; _; _; _; _; generally have

   forward chaining (see :ref:`structure_ssr`)

.. tacn:: wlog {? suff } {? @i_item } : {* {| @gen_item | @clear_switch } } / @term

   specializing (see :ref:`structure_ssr`)

.. tacn:: suff {* @i_item } {? @i_pattern } {+ @ssr_binder } : @term {? by @tactic }
          suffices {* @i_item } {? @i_pattern } {+ @ssr_binder } : @term {? by @tactic }
          suff {? have } {? @clear_switch } {? @i_pattern } : @term {? by @tactic }
          suffices {? have } {? @clear_switch } {? @i_pattern } : @term {? by @tactic }
   :name: suff; suffices; _; _

   backchaining (see :ref:`structure_ssr`)

.. tacv:: pose @ident := @term

   local definition (see :ref:`definitions_ssr`)

.. tacv:: pose @ident {+ @ssr_binder } := @term

   local function definition

.. tacv:: pose fix @fix_decl

   local fix definition

.. tacv:: pose cofix @fix_decl

   local cofix definition

.. tacn:: set @ident {? : @term } := {? @occ_switch } {| @term | ( @c_pattern) }
   :name: set (ssreflect)

   abbreviation (see :ref:`abbreviations_ssr`)

.. tacn:: unlock {* {? @r_prefix } @ident }

   unlock (see :ref:`locking_ssr`)

.. tacn:: congr {? @natural } @term

   congruence (see :ref:`congruence_ssr`)


Tacticals
~~~~~~~~~

.. prodn:: tactic += @d_tactic {? @ident } : {+ @d_item } {? @clear_switch }

discharge (see :ref:`discharge_ssr`)

.. prodn:: tactic += @tactic => {+ @i_item }

introduction (see :ref:`introduction_ssr`)

.. prodn:: tactic += @tactic in {+ {| @gen_item | @clear_switch } } {? * }

localization (see :ref:`localization_ssr`)

.. prodn:: tactic += do {? @mult } {| @tactic | [ {+| @tactic } ] }

iteration (see :ref:`iteration_ssr`)

.. prodn:: tactic += @tactic ; {| first | last } {? @natural } {| @tactic | [ {+| @tactic } ] }

selector (see :ref:`selectors_ssr`)

.. prodn:: tactic += @tactic ; {| first | last } {? @natural }

rotation (see :ref:`selectors_ssr`)

.. prodn:: tactic += by {| @tactic | [ {*| @tactic } ] }

closing (see :ref:`terminators_ssr`)

Commands
~~~~~~~~

.. cmd:: Hint View for {| move | apply } / @ident {? | @natural }

   view hint declaration (see :ref:`declaring_new_hints_ssr`)

.. cmd:: Hint View for apply // @ident {? @natural }

   right hand side double , view hint declaration (see :ref:`declaring_new_hints_ssr`)

.. cmd:: Prenex Implicits {+ @ident }

   prenex implicits declaration (see :ref:`parametric_polymorphism_ssr`)

Settings
~~~~~~~~

.. flag:: Debug Ssreflect

   *Developer only.* Print debug information on reflect.

.. flag:: Debug SsrMatching

   *Developer only.* Print debug information on SSR matching.

.. rubric:: Footnotes

.. [#1] Unfortunately, even after a call to the ``Set Printing All`` command,
  some occurrences are still not displayed to the user, essentially the
  ones possibly hidden in the predicate of a dependent match structure.
.. [#2] Thus scripts that depend on bound variable names, e.g., via intros
  or with, are inherently fragile.
.. [#3] The name ``subnK`` reads as “right cancellation rule for ``nat``
  subtraction”.
.. [#4] Also, a slightly different variant may be used for the first :token:`d_item`
  of ``case`` and ``elim``; see Section :ref:`type_families_ssr`.
.. [#5] Except that ``/=`` does not expand the local definitions created by the
  |SSR| ``in`` tactical.
.. [#6] |SSR| reserves all identifiers of the form “_x_”, which is
  used for such generated names.
.. [#7] More precisely, it should have a quantified inductive type with a
  assumptions and m − a constructors.
.. [#8] This is an implementation feature: there is no such obstruction
  in the metatheory.
.. [#9] The current state of the proof shall be displayed by the ``Show
  Proof`` command of Rocq proof mode.
.. [#10] A simple proof context entry is a naked identifier (i.e., not between
  parentheses) designating a context entry that is not a section variable.
