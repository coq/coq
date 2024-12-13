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
     rewrite_rule ::= {? @univ_decl %|- } @rw_pattern => @term

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
     | fun {+ ({+ @name } {? : @rw_pattern_arg}) } => @rw_pattern_arg
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


   .. rocqtop:: all warn

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
Universe levels and sort quality variables must be declared with the notation :n:`@{q1 q2|u1 u2+|+}`
(the same notation as universe instance declarations);
each variable must appear exactly once in the pattern.
If any universe level isn't bound in the rule,
as is often the case with the level of a pattern variable when it is a type,
you need to make the universe instance extensible (with the final +).
Universe level constraints, as inferred from the pattern, must imply those given,
which in turn must imply the constraints needed for the replacement.
You can make the declared constraints extensible
so all inferred constraints from the left-hand side are used for the replacement.

   .. rocqtop:: reset all warn

      #[universes(polymorphic)] Symbol raise@{q|u|} : forall (A : Type@{q|u}), A.
      Rewrite Rule raise_nat :=
        @{q|u+|+} |- raise@{q|u} (forall (x : ?A), ?P) => fun (x : ?A) => raise@{q|u} ?P.

Rewrite rules, type preservation, confluence and termination
------------------------------------------------------------

Currently, rewrite rules do not ensure that types must be preserved.
There is a superficial check that the replacement needs to be typed
against the type inferred for the pattern (for an unclear definition of type of a pattern),
but it is known to be incomplete and only emits a warning if failed.
This then means that reductions using rewrite rules have no reason to preserve well-typedness at all.
The responsibility of ensuring type preservation falls on the user entirely.

Similarly, neither confluence nor termination are checked by the compiler.

There are future plans to add a check on confluence using the triangle criterion :cite:`TotR21`
and a more complete check on type preservation.

Compatibility with the eta laws
-------------------------------

Currently, pattern matching against rewrite rules pattern cannot do eta-expansion or contraction,
which means that it cannot properly match against terms of functional types or primitive records.
As with type preservation, a check is done to test whether this may happen,
but it is not complete (false positives) and thus only emits a warning if failed.

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
