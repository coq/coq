.. this should be just "_program", but refs to it don't work

.. _programs:

Program
========

:Author: Matthieu Sozeau

We present here the |Program| tactic commands, used to build
certified |Coq| programs, elaborating them from their algorithmic
skeleton and a rich specification :cite:`sozeau06`. It can be thought of as a
dual of :ref:`Extraction <extraction>`. The goal of |Program| is to
program as in a regular functional programming language whilst using
as rich a specification as desired and proving that the code meets the
specification using the whole |Coq| proof apparatus. This is done using
a technique originating from the “Predicate subtyping” mechanism of
PVS :cite:`Rushby98`, which generates type checking conditions while typing a
term constrained to a particular type. Here we insert existential
variables in the term, which must be filled with proofs to get a
complete |Coq| term. |Program| replaces the |Program| tactic by Catherine
Parent :cite:`Parent95b` which had a similar goal but is no longer maintained.

The languages available as input are currently restricted to |Coq|’s
term language, but may be extended to OCaml, Haskell and
others in the future. We use the same syntax as |Coq| and permit to use
implicit arguments and the existing coercion mechanism. Input terms
and types are typed in an extended system (Russell) and interpreted
into |Coq| terms. The interpretation process may produce some proof
obligations which need to be resolved to create the final term.


.. _elaborating-programs:

Elaborating programs
---------------------

The main difference from |Coq| is that an object in a type :g:`T : Set` can
be considered as an object of type :g:`{x : T | P}` for any well-formed
:g:`P : Prop`. If we go from :g:`T` to the subset of :g:`T` verifying property
:g:`P`, we must prove that the object under consideration verifies it. Russell
will generate an obligation for every such coercion. In the other direction,
Russell will automatically insert a projection.

Another distinction is the treatment of pattern matching. Apart from
the following differences, it is equivalent to the standard match
operation (see :ref:`extendedpatternmatching`).


+ Generation of equalities. A match expression is always generalized
  by the corresponding equality. As an example, the expression:

  ::

   match x with
   | 0 => t
   | S n => u
   end.

  will be first rewritten to:

  ::

   (match x as y return (x = y -> _) with
   | 0 => fun H : x = 0 -> t
   | S n => fun H : x = S n -> u
   end) (eq_refl x).

  This permits to get the proper equalities in the context of proof
  obligations inside clauses, without which reasoning is very limited.

+ Generation of disequalities. If a pattern intersects with a previous
  one, a disequality is added in the context of the second branch. See
  for example the definition of div2 below, where the second branch is
  typed in a context where :g:`∀ p, _ <> S (S p)`.
+ Coercion. If the object being matched is coercible to an inductive
  type, the corresponding coercion will be automatically inserted. This
  also works with the previous mechanism.


There are options to control the generation of equalities and
coercions.

.. flag:: Program Cases

   This controls the special treatment of pattern matching generating equalities
   and disequalities when using |Program| (it is on by default). All
   pattern-matches and let-patterns are handled using the standard algorithm
   of |Coq| (see :ref:`extendedpatternmatching`) when this option is
   deactivated.

.. flag:: Program Generalized Coercion

   This controls the coercion of general inductive types when using |Program|
   (the option is on by default). Coercion of subset types and pairs is still
   active in this case.

.. _syntactic_control:

Syntactic control over equalities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To give more control over the generation of equalities, the
type checker will fall back directly to |Coq|’s usual typing of dependent
pattern matching if a ``return`` or ``in`` clause is specified. Likewise, the
if construct is not treated specially by |Program| so boolean tests in
the code are not automatically reflected in the obligations. One can
use the :g:`dec` combinator to get the correct hypotheses as in:

.. coqtop:: in

   Require Import Program Arith.

.. coqtop:: all

   Program Definition id (n : nat) : { x : nat | x = n } :=
     if dec (leb n 0) then 0
     else S (pred n).

The :g:`let` tupling construct :g:`let (x1, ..., xn) := t in b` does not
produce an equality, contrary to the let pattern construct
:g:`let '(x1,..., xn) := t in b`.
Also, :g:`term :>` explicitly asks the system to
coerce term to its support type. It can be useful in notations, for
example:

.. coqtop:: all

   Notation " x `= y " := (@eq _ (x :>) (y :>)) (only parsing).

This notation denotes equality on subset types using equality on their
support types, avoiding uses of proof-irrelevance that would come up
when reasoning with equality on the subset types themselves.

The next two commands are similar to their standard counterparts
:cmd:`Definition` and :cmd:`Fixpoint`
in that they define constants. However, they may require the user to
prove some goals to construct the final definitions.


.. _program_definition:

Program Definition
~~~~~~~~~~~~~~~~~~

.. cmd:: Program Definition @ident := @term

   This command types the value term in Russell and generates proof
   obligations. Once solved using the commands shown below, it binds the
   final |Coq| term to the name ``ident`` in the environment.

   .. exn:: @ident already exists.
      :name: @ident already exists. (Program Definition)
      :undocumented:

   .. cmdv:: Program Definition @ident : @type := @term

      It interprets the type ``type``, potentially generating proof
      obligations to be resolved. Once done with them, we have a |Coq|
      type |type_0|. It then elaborates the preterm ``term`` into a |Coq|
      term |term_0|, checking that the type of |term_0| is coercible to
      |type_0|, and registers ``ident`` as being of type |type_0| once the
      set of obligations generated during the interpretation of |term_0|
      and the aforementioned coercion derivation are solved.

      .. exn:: In environment … the term: @term does not have type @type. Actually, it has type ...
         :undocumented:

   .. cmdv:: Program Definition @ident @binders : @type := @term

      This is equivalent to:

      :g:`Program Definition ident : forall binders, type := fun binders => term`.

      .. TODO refer to production in alias

.. seealso:: Sections :ref:`vernac-controlling-the-reduction-strategies`, :tacn:`unfold`

.. _program_fixpoint:

Program Fixpoint
~~~~~~~~~~~~~~~~

.. cmd:: Program Fixpoint @ident @binders {? {@order}} : @type := @term

   The optional order annotation follows the grammar:

   .. productionlist:: orderannot
      order      : measure `term` (`term`)? | wf `term` `term`

   + :g:`measure f ( R )` where :g:`f` is a value of type :g:`X` computed on
     any subset of the arguments and the optional (parenthesised) term
     ``(R)`` is a relation on ``X``. By default ``X`` defaults to ``nat`` and ``R``
     to ``lt``.

   + :g:`wf R x` which is equivalent to :g:`measure x (R)`.

   The structural fixpoint operator behaves just like the one of |Coq| (see
   :cmd:`Fixpoint`), except it may also generate obligations. It works
   with mutually recursive definitions too.

.. coqtop:: reset in

   Require Import Program Arith.

.. coqtop:: all

   Program Fixpoint div2 (n : nat) : { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
     match n with
     | S (S p) => S (div2 p)
     | _ => O
     end.

Here we have one obligation for each branch (branches for :g:`0` and
``(S 0)`` are automatically generated by the pattern matching
compilation algorithm).

.. coqtop:: all

   Obligation 1.

.. coqtop:: reset none

   Require Import Program Arith.

One can use a well-founded order or a measure as termination orders
using the syntax:

.. coqtop:: in

   Program Fixpoint div2 (n : nat) {measure n} : { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
     match n with
     | S (S p) => S (div2 p)
     | _ => O
     end.



.. caution:: When defining structurally recursive functions, the generated
   obligations should have the prototype of the currently defined
   functional in their context. In this case, the obligations should be
   transparent (e.g. defined using :g:`Defined`) so that the guardedness
   condition on recursive calls can be checked by the kernel’s type-
   checker. There is an optimization in the generation of obligations
   which gets rid of the hypothesis corresponding to the functional when
   it is not necessary, so that the obligation can be declared opaque
   (e.g. using :g:`Qed`). However, as soon as it appears in the context, the
   proof of the obligation is *required* to be declared transparent.

   No such problems arise when using measures or well-founded recursion.

.. _program_lemma:

Program Lemma
~~~~~~~~~~~~~

.. cmd:: Program Lemma @ident : @type

   The Russell language can also be used to type statements of logical
   properties. It will generate obligations, try to solve them
   automatically and fail if some unsolved obligations remain. In this
   case, one can first define the lemma’s statement using :g:`Program
   Definition` and use it as the goal afterwards. Otherwise the proof
   will be started with the elaborated version as a goal. The
   :g:`Program` prefix can similarly be used as a prefix for
   :g:`Variable`, :g:`Hypothesis`, :g:`Axiom` etc.

.. _solving_obligations:

Solving obligations
--------------------

The following commands are available to manipulate obligations. The
optional identifier is used when multiple functions have unsolved
obligations (e.g. when defining mutually recursive blocks). The
optional tactic is replaced by the default one if not specified.

.. cmd:: {? Local|Global} Obligation Tactic := @tactic
   :name: Obligation Tactic

   Sets the default obligation solving tactic applied to all obligations
   automatically, whether to solve them or when starting to prove one,
   e.g. using :g:`Next`. :g:`Local` makes the setting last only for the current
   module. Inside sections, local is the default.

.. cmd:: Show Obligation Tactic

   Displays the current default tactic.

.. cmd:: Obligations {? of @ident}

   Displays all remaining obligations.

.. cmd:: Obligation num {? of @ident}

   Start the proof of obligation num.

.. cmd:: Next Obligation {? of @ident}

   Start the proof of the next unsolved obligation.

.. cmd:: Solve Obligations {? {? of @ident} with @tactic}

   Tries to solve each obligation of ``ident`` using the given ``tactic`` or the default one.

.. cmd:: Solve All Obligations {? with @tactic}

   Tries to solve each obligation of every program using the given
   tactic or the default one (useful for mutually recursive definitions).

.. cmd:: Admit Obligations {? of @ident}

   Admits all obligations (of ``ident``).

   .. note:: Does not work with structurally recursive programs.

.. cmd:: Preterm {? of @ident}

   Shows the term that will be fed to the kernel once the obligations
   are solved. Useful for debugging.

.. flag:: Transparent Obligations

   Controls whether all obligations should be declared as transparent
   (the default), or if the system should infer which obligations can be
   declared opaque.

.. flag:: Hide Obligations

   Controls whether obligations appearing in the
   term should be hidden as implicit arguments of the special
   constantProgram.Tactics.obligation.

.. flag:: Shrink Obligations

   *Deprecated since 8.7*

   This option (on by default) controls whether obligations should have
   their context minimized to the set of variables used in the proof of
   the obligation, to avoid unnecessary dependencies.

The module :g:`Coq.Program.Tactics` defines the default tactic for solving
obligations called :g:`program_simpl`. Importing :g:`Coq.Program.Program` also
adds some useful notations, as documented in the file itself.

.. _program-faq:

Frequently Asked Questions
---------------------------


.. exn:: Ill-formed recursive definition.

  This error can happen when one tries to define a function by structural
  recursion on a subset object, which means the |Coq| function looks like:

  ::

     Program Fixpoint f (x : A | P) := match x with A b => f b end.

  Supposing ``b : A``, the argument at the recursive call to ``f`` is not a
  direct subterm of ``x`` as ``b`` is wrapped inside an ``exist`` constructor to
  build an object of type ``{x : A | P}``.  Hence the definition is
  rejected by the guardedness condition checker.  However one can use
  wellfounded recursion on subset objects like this:

  ::

     Program Fixpoint f (x : A | P) { measure (size x) } :=
       match x with A b => f b end.

  One will then just have to prove that the measure decreases at each
  recursive call. There are three drawbacks though:

    #. A measure function has to be defined;
    #. The reduction is a little more involved, although it works well
       using lazy evaluation;
    #. Mutual recursion on the underlying inductive type isn’t possible
       anymore, but nested mutual recursion is always possible.
