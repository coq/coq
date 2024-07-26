:COQTOP_ARGS: -allow-rewrite-rules

.. _rewrite_rules:

User-defined rewrite rules
==========================

.. warning::

   Rewrite rules are highly experimental.

   In particular, ill-typed rewrite rules will lead to mistyped expressions,
   and manipulating these will most often result in inconsistencies and anomalies.


This section describes the extension of Rocq's reduction mechanisms with user-defined rewrite rules,
as a means to extend definitional equality. It should not be confused with the :ref:`rewrite tactic <rewritingexpressions>`
or :ref:`setoid rewriting <generalizedrewriting>` which operate on propositional equality and other relations which are defined in Rocq.
This extension is described in :cite:`Rew24`, following the theory developed in :cite:`TotR21`.

Rewrite rules need to be enabled by passing the option ``-allow-rewrite-rules``
to the Rocq program.

   .. exn:: Rewrite rule declaration requires passing the flag "-allow-rewrite-rules".
      :undocumented:

Symbols
-----------------

Rewrite rules operate on symbols, which are their own kind of constants.
They stand in-between defined constants and axioms,
in that they don't always reduce as defined constants do,
but they may still reduce using the provided rules, unlike axioms.

.. cmd:: {| Symbol | Symbols } {| @assumpt | {+ ( @assumpt ) } }
   :name: Symbol; Symbols

   Binds an :n:`@ident` to a :n:`@type` as a symbol.

   .. rocqtop:: in

      Symbol pplus : nat -> nat -> nat.
      Notation "a ++ b" := (pplus a b).

Rewrite rules
---------------
.. cmd:: Rewrite {| Rule | Rules } @ident := {? %| } {+| @rewrite_rule }
  :name: Rewrite Rule; Rewrite Rules

  .. insertprodn rewrite_rule rewrite_rule

  .. prodn::
     rewrite_rule ::= @rw_pattern => @term

Declares a named block of rewrite rules. The name is declared in the same namespace as constants and inductives.

Rewrite rules have two parts named pattern (left-hand side) and replacement (right-hand side).
Patterns are a subclass of :n:`@term`\s described :ref:`below<Pattern syntax>`,
while replacements are regular :n:`@term`\s,
which can also refer to the pattern variables matched by the pattern with the :n:`?@name` syntax.
When a rule is applied, the term is matched against the pattern,
subterms aligned with pattern variables are collected
and then substituted into the replacement, which is returned.

  .. rocqtop:: all

     Rewrite Rule pplus_rewrite :=
     | ?n ++ 0 => ?n
     | ?n ++ S ?m => S (?n ++ ?m)
     | 0 ++ ?n => ?n
     | S ?n ++ ?m => S (?n ++ ?m).

.. _Pattern syntax:

Pattern syntax
--------------

Patterns are a subclass of :n:`@term`\s which are rigid enough to be matched against.
Informally, they are terms with pattern variables (:n:`?@name`),
where those may not appear on the left of applications or as the discriminee of a match or a primitive projection;
furthermore a pattern may not have let-bindings, (co-)fixpoints or non-symbol constants.

As a formal grammar, it is easier to understand them with the separation between head-pattern (:n:`@rw_head_pattern`)
and eliminations (non-base-case constructions for :n:`@rw_pattern`):

  .. prodn::
     rw_pattern ::= @rw_head_pattern
     | @rw_pattern {+ @rw_pattern_arg }
     | @rw_pattern .( @qualid {? @univ_annot } )
     | match @rw_pattern {? as @name } {? in @pattern } {? return @rw_pattern_arg } with {? | } {*| @pattern => @rw_pattern_arg } end
     rw_head_pattern ::= @ident
     | @qualid {? @univ_annot }
     | fun {+ ({+ @name } {? : @rw_pattern_arg}) } => @rw_pattern
     | forall {+ ({+ @name } {? : @rw_pattern_arg}) }, @rw_pattern_arg
     rw_pattern_arg ::= ?@name
     | _
     | @rw_pattern

where :n:`@qualid {? @univ_annot }` (in the second line for :n:`@rw_head_pattern`) can refer to symbols, sorts, inductives and constructors, but not arbitrary constants.
The projections must be primitive to be allowed.

Finally, a valid pattern needs its head head-pattern to be a symbol.


Higher-order pattern holes
--------------------------

Patterns with lambdas (:n:`fun`), products (:n:`forall`) and :n:`match`\es
introduce new variables in the context which need to be substituted in the replacement.
To this end, the user can add what to substitute each new variable with,
using the syntax :n:`?@name@%{{+; @name := @term }%}`.
Note that if in the replacement, the context was extended with a variable bearing the same name,
this explicit substitution is inferred automatically (like for existential variable instantiations).


   .. rocqtop:: reset all warn

      Symbol raise : forall (A : Type), A.
      Rewrite Rule raise_nat :=
        match raise nat as n return ?P
        with 0 => _ | S _ => _ end
        => raise ?P@{n := raise nat}.

      Symbol id : forall (A : Type), A -> A.
      Rewrite Rule id_rew :=
        id (forall (x : ?A), ?P) ?f => fun (x : ?A) => id ?P (?f x).

Universe polymorphic rules
--------------------------

Rewrite rules support universe and sort quality polymorphism.
As with pattern variables, universe levels and sort quality variables
must appear linearly (not more than once each) in the pattern.
Sort quality variables which appear only in :term:`relevance marks <relevance mark>` in the replacement
will be detected if they also appear in a relevance mark in the pattern, such that
they can be substituted when the rule is applied (otherwise you will get an undeclared sort quality error).

   .. rocqtop:: reset all warn

      #[universes(polymorphic)] Symbol raise@{q|u|} : forall (A : Type@{q|u}), A.
      Rewrite Rule raise_nat :=
        raise@{q|u} (forall (x : ?A), ?P) => fun (x : ?A) => raise@{q|u} ?P.

Rewrite rules, type preservation, confluence and termination
------------------------------------------------------------

The rewrite rules are typechecked so that all substituted replacements
have the type that the term being rewritten has (as described in :cite:`Rew24`).
This means that the check is more stringent than ensuring the two sides have a shared type.
This also means that the pattern is typechecked differently from regular terms,
with an especially more restricted unification engine,
which leads to the typechecker refusing rules that do respect the criterion.
For this reason, the typechecker only emits warnings when it fails to verify the rule,
letting the user take responsibility over the correctness of the rule.

Rocq currently doesn't check for confluence of the rewrite rules,
even though it is required for the invariants that the typechecker uses.
There are plans to add a check using the triangle criterion described in :cite:`TotR21`.

Rocq doesn't check for termination of the rewrite rules either.
Indeed, non-terminating rules are generally fine except for one thing:
the typechecker itself might not always terminate anymore.
Unlike the previous two properties, non-termination cannot cause crashes or anomalies.

Compatibility with the eta laws
-------------------------------

Currently, pattern matching against rewrite rules pattern cannot do eta-expansion or contraction,
which means that it cannot properly match against terms of functional types or primitive records.
Rocq checks whether this may happen, but the check is imperfect (it reports false positives).
Therefore, the check fails by only emitting a warning, similar to the check for type preservation.

Level of support
----------------

Rewrite rules have been integrated into the kernel and the most used parts of the upper layers.
Notably, reduction machines simpl, cbn and cbv can reduce on rewrite rules,
with some limitations (e.g. simpl cannot reduce on rules which contain a match).
Also, regular unification can work with rewrite rules,
as well as apply's unification mechanism in a limited manner
(only if the pattern contains no match or projections).

On the other hand, some operations are not supported,
such as declaring rules in sections and some interactions with modules.
Since rewrite rules may introduce untyped terms,
which the VM and native reduction machines don't support (risk of segfault or code injection),
they are turned off when rewrite rules are enabled.
