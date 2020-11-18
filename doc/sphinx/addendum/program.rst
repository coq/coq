.. this should be just "_program", but refs to it don't work

.. _programs:

Program
========

:Author: Matthieu Sozeau

We present here the |Program| tactic commands, used to build
certified Coq programs, elaborating them from their algorithmic
skeleton and a rich specification :cite:`sozeau06`. It can be thought of as a
dual of :ref:`Extraction <extraction>`. The goal of |Program| is to
program as in a regular functional programming language whilst using
as rich a specification as desired and proving that the code meets the
specification using the whole Coq proof apparatus. This is done using
a technique originating from the “Predicate subtyping” mechanism of
PVS :cite:`Rushby98`, which generates type checking conditions while typing a
term constrained to a particular type. Here we insert existential
variables in the term, which must be filled with proofs to get a
complete Coq term. |Program| replaces the |Program| tactic by Catherine
Parent :cite:`Parent95b` which had a similar goal but is no longer maintained.

The languages available as input are currently restricted to Coq’s
term language, but may be extended to OCaml, Haskell and
others in the future. We use the same syntax as Coq and permit to use
implicit arguments and the existing coercion mechanism. Input terms
and types are typed in an extended system (Russell) and interpreted
into Coq terms. The interpretation process may produce some proof
obligations which need to be resolved to create the final term.


.. _elaborating-programs:

Elaborating programs
--------------------

The main difference from Coq is that an object in a type :g:`T : Set` can
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


There are flags to control the generation of equalities and
coercions.

.. flag:: Program Cases

   Controls the special treatment of pattern matching generating equalities
   and disequalities when using |Program| (it is on by default). All
   pattern-matches and let-patterns are handled using the standard algorithm
   of Coq (see :ref:`extendedpatternmatching`) when this flag is
   deactivated.

.. flag:: Program Generalized Coercion

   Controls the coercion of general inductive types when using |Program|
   (the flag is on by default). Coercion of subset types and pairs is still
   active in this case.

.. flag:: Program Mode

   Enables the program mode, in which 1) typechecking allows subset coercions and
   2) the elaboration of pattern matching of :cmd:`Fixpoint` and
   :cmd:`Definition` acts as if the :attr:`program` attribute has been
   used, generating obligations if there are unresolved holes after
   typechecking.

.. attr:: program{? = {| yes | no } }
   :name: program; Program

   This :term:`boolean attribute` allows using or disabling the Program mode on a specific
   definition.  An alternative and commonly used syntax is to use the legacy ``Program``
   prefix (cf. :n:`@legacy_attr`) as it is elsewhere in this chapter.

.. _syntactic_control:

Syntactic control over equalities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To give more control over the generation of equalities, the
type checker will fall back directly to Coq’s usual typing of dependent
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

A :cmd:`Definition` command with the :attr:`program` attribute types
the value term in Russell and generates proof
obligations. Once solved using the commands shown below, it binds the
final Coq term to the name :n:`@ident` in the environment.

:n:`Program Definition @ident : @type := @term`

Interprets the type :n:`@type`, potentially generating proof
obligations to be resolved. Once done with them, we have a Coq
type :n:`@type__0`. It then elaborates the preterm :n:`@term` into a Coq
term :n:`@term__0`, checking that the type of :n:`@term__0` is coercible to
:n:`@type__0`, and registers :n:`@ident` as being of type :n:`@type__0` once the
set of obligations generated during the interpretation of :n:`@term__0`
and the aforementioned coercion derivation are solved.

.. seealso:: Sections :ref:`vernac-controlling-the-reduction-strategies`, :tacn:`unfold`

.. _program_fixpoint:

Program Fixpoint
~~~~~~~~~~~~~~~~

A :cmd:`Fixpoint` command with the :attr:`program` attribute may also generate obligations. It works
with mutually recursive definitions too.  For example:

.. coqtop:: reset in

   Require Import Program Arith.

.. coqtop:: all

   Program Fixpoint div2 (n : nat) : { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
     match n with
     | S (S p) => S (div2 p)
     | _ => O
     end.

The :cmd:`Fixpoint` command may include an optional :n:`@fixannot` annotation, which can be:

+ :g:`measure f R` where :g:`f` is a value of type :g:`X` computed on
  any subset of the arguments and the optional term
  :g:`R` is a relation on :g:`X`. :g:`X` defaults to :g:`nat` and :g:`R`
  to :g:`lt`.

+ :g:`wf R x` which is equivalent to :g:`measure x R`.

.. todo see https://github.com/coq/coq/pull/12936#discussion_r492747830

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

A :cmd:`Lemma` command with the :attr:`program` attribute uses the Russell
language to type statements of logical
properties. It generates obligations, tries to solve them
automatically and fails if some unsolved obligations remain. In this
case, one can first define the lemma’s statement using :cmd:`Definition`
and use it as the goal afterwards. Otherwise the proof
will be started with the elaborated version as a goal. The
:attr:`Program` attribute can similarly be used with
:cmd:`Variable`, :cmd:`Hypothesis`, :cmd:`Axiom` etc.

.. _solving_obligations:

Solving obligations
-------------------

The following commands are available to manipulate obligations. The
optional identifier is used when multiple functions have unsolved
obligations (e.g. when defining mutually recursive blocks). The
optional tactic is replaced by the default one if not specified.

.. cmd:: Obligation Tactic := @ltac_expr
   :name: Obligation Tactic

   Sets the default obligation solving tactic applied to all obligations
   automatically, whether to solve them or when starting to prove one,
   e.g. using :cmd:`Next Obligation`.

   This command supports the :attr:`local` and :attr:`global` attributes.
   :attr:`local` makes the setting last only for the current
   module. :attr:`local` is the default inside sections while :attr:`global`
   otherwise.

.. cmd:: Show Obligation Tactic

   Displays the current default tactic.

.. cmd:: Obligations {? of @ident }

   Displays all remaining obligations.

.. cmd:: Obligation @natural {? of @ident } {? : @type {? with @ltac_expr } }

   Start the proof of obligation :token:`natural`.

.. cmd:: Next Obligation {? of @ident } {? with @ltac_expr }

   Start the proof of the next unsolved obligation.

.. cmd:: Solve Obligations {? of @ident } {? with @ltac_expr }

   Tries to solve each obligation of :token:`ident` using the given :token:`ltac_expr` or the default one.

.. cmd:: Solve All Obligations {? with @ltac_expr }

   Tries to solve each obligation of every program using the given
   tactic or the default one (useful for mutually recursive definitions).

.. cmd:: Admit Obligations {? of @ident }

   Admits all obligations (of :token:`ident`).

   .. note:: Does not work with structurally recursive programs.

.. cmd:: Preterm {? of @ident }

   Shows the term that will be fed to the kernel once the obligations
   are solved. Useful for debugging.

.. flag:: Transparent Obligations

   Controls whether all obligations should be declared as transparent
   (the default), or if the system should infer which obligations can be
   declared opaque.

.. flag:: Hide Obligations

   .. deprecated:: 8.12

   Controls whether obligations appearing in the
   term should be hidden as implicit arguments of the special
   constant ``Program.Tactics.obligation``.

The module :g:`Coq.Program.Tactics` defines the default tactic for solving
obligations called :g:`program_simpl`. Importing :g:`Coq.Program.Program` also
adds some useful notations, as documented in the file itself.

.. _program-faq:

Frequently Asked Questions
---------------------------


.. exn:: Ill-formed recursive definition.

  This error can happen when one tries to define a function by structural
  recursion on a subset object, which means the Coq function looks like:

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
