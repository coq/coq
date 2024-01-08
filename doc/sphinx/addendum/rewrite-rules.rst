.. _rewrite_rules:

User-defined rewrite rules
==========================

.. warning::

   The status of rewrite rules is highly experimental.

   In particular, ill-typed rewrite rules will lead to mistyped expressions,
   and manipulating these will most often result in anomalies.


This section describes the extension of Coq's reduction mechanisms with user-defined rewrite rules,
as a means to extend definitional equality. It should not be confused with the :ref:`rewrite tactic <rewritingexpressions>`
or :ref:`setoid rewriting <generalizedrewriting>` which operate on propositional equality and other relations which are defined in Coq.

The use of rewrite rules is guarded behind a flag, which can be enabled
either by passing ``-allow-rewrite-rules`` to the
Coq program or by turning the :flag:`Allow Rewrite Rules` flag on.

.. flag:: Allow Rewrite Rules

   This :term:`flag` enables the use of rewrite rules.
   It is disabled by default and cannot be disabled once enabled.
   The command-line flag ``-allow-rewrite-rules`` enables rewrite rules at
   startup.

   .. exn:: Rewrite rule declaration requires enabling the flag "Allow Rewrite Rules".
      :undocumented:

Symbols
-----------------

Rewrite rules operate on symbols, which are their own kind of constants.
They stand in-between defined constants and axioms,
in that they don't always reduce as defined constants do,
but they may still reduce using the provided rules, unlike axioms.

.. cmd:: {| Symbol | Symbols } {| {+ ( @assumpt ) } | @assumpt }
   :name: Symbol; Symbols

   As a command, `Symbol` binds an :n:`ident` to a :n:`type` as a symbol.

   .. coqtop:: in

      Set Allow Rewrite Rules.
      Symbol pplus : nat -> nat -> nat.
      Notation "a ++ b" := (pplus a b).

Rewrite rules
---------------

  .. insertprodn rewrite_rule rewrite_rule

  .. prodn::
     rewrite_rule ::= {? @univ_decl %|- } @rw_pattern ==> @term

Rewrite rules have two parts simply named left-hand side or pattern and right-hand side.
When a rule is applied, the term is matched against the pattern,
subterms aligned with pattern variables are collected
and substituted into the right-hand side which is returned.

.. cmd:: Rewrite {| Rule | Rules } @ident := {? %| } {+| @rewrite_rule }
  :name: Rewrite Rule; Rewrite Rules

   The command declares a named block of rewrite rules.

  .. coqtop:: all

     Rewrite Rule pplus_rewrite :=
     | ?n ++ 0 ==> ?n
     | ?n ++ S ?m ==> S (?n ++ ?m)
     | 0 ++ ?n ==> ?n
     | S ?n ++ ?m ==> S (?n ++ ?m).

Pattern syntax
--------------

Patterns are a subset of terms which follow a more rigid syntax.
It is easier to understand them as being a rigid head-pattern, inside of an elimination context:

  .. prodn::
     rw_head_pattern ::= @qualid {? @univ_annot }
     | fun ({+ @name } {? : @rw_pattern_arg}) => @rw_pattern_arg
     | forall ({+ @name } {? : @rw_pattern_arg}), @rw_pattern_arg
     elim_context ::= []
     | @elim_context {+ @rw_pattern_arg }
     | @elim_context .( @qualid {? @univ_annot } )
     | match @elim_context {? as @name } {? in @pattern } {? return @rw_pattern_arg } with {*| @pattern => @rw_pattern_arg } end
     rw_pattern ::= @elim_context[@rw_head_pattern]
     rw_pattern_arg ::= ?@name | _ | @rw_pattern

where :n:`@qualid {? @univ_annot }` (in the first line) can refer to bound variables, symbols, sorts, inductives and constructors, but not arbitrary constants.
The projections must be primitive to be allowed.

In a few words, patterns are terms with pattern variables (:n:`?@name`),
but those may not appear on the left of applications or as the discriminee of a match or a primitive projection;
furthermore a pattern may not have let-bindings or non-symbol constants.

Finally, a valid pattern needs its head head-pattern to be a symbol.


Right-hand sides
----------------

Rewrite rules right-hand sides are :n:`@term`\s, which can also refer to matched pattern variables in the pattern with the :n:`?@name` syntax.


Higher-order pattern holes
--------------------------

Patterns with lambdas (:n:`fun`), products (:n:`forall`) and :n:`match`\es introduce new variables in the context which need to be substituted in the right-hand side.
To this end, the user can add what to substitute each new variable with, using the syntax :n:`?@name@%{{+; @name := @term }%}`.
Note that if in the right-hand side, the context was extended with a variable bearing the same name, this explicit substitution is inferred automatically (like for existential variable instantiations).


   .. coqtop:: all warn

      Symbol raise : forall (A : Type), A.
      Rewrite Rule raise_nat :=
        match raise nat as n return ?P
        with 0 => _ | S _ => _ end
        ==> raise ?P@{n := raise nat}.

      Symbol id : forall (A : Type), A -> A.
      Rewrite Rule id_rew :=
        id (forall (x : ?A), ?P) ?f ==> fun (x : ?A) => id ?P (?f x).

Universe polymorphic rules
--------------------------

Rewrite rules support universe and sort quality polymorphism.
Universe levels and sort quality variables must be declared with the notation :n:`@{q1 q2|u1 u2+|+}` (the same notation as universe instance declarations);
each variable must appear exactly once in the pattern.
If any universe level isn't bound in the rule, as is often the case with the level of a pattern variable when it is a type, you need to make the universe instance extensible (with the final +).
Universe level constraints, as inferred from the pattern, must imply those given, which in turn must imply the constraints needed for the right-hand side.
You can make the declared constraints extensible so all inferred constraints from the left-hand side are used for the right-hand side.

   .. coqtop:: reset all warn

      Set Allow Rewrite Rules.
      #[universes(polymorphic)] Symbol raise@{q|u|} : forall (A : Type@{q|u}), A.
      Rewrite Rule raise_nat :=
        @{q|u+|+} |- raise@{q|u} (forall (x : ?A), ?P) ==> fun (x : ?A) => raise@{q|u} ?P.

Rewrite rules, type preservation, confluence and termination
------------------------------------------------------------

Currently, rewrite rules do not ensure that types must be preserved.
There is a superficial check that the right-hand side needs to be typed
against the type inferred for the pattern (for an unclear definition of type of a pattern),
but it is known to be incomplete and only emits a warning if failed.
This then means that reductions using rewrite rules have no reason to preserve welltypedness at all.
The responsibility of ensuring type preservation falls on the user entirely.

Similarly, neither confluence nor termination are checked by the compiler.

There are future plans to add a check on confluence using the triangle criterion :cite:`TotR21` and a more complete check on type preservation.

Compatibility with the eta laws
-------------------------------

Currently, pattern matching against rewrite rules pattern cannot do eta-expansion or contraction,
which means that it cannot properly match against terms of functional types or primitive records.
As with type preservation, a check is done to test whether this may happen, but it is not complete (false positives)
and thus only emits a warning if failed.

Level of support
----------------

Rewrite rules have been integrated into the kernel and the most used parts of the upper layers.
Notably, reduction machines simpl, cbn and cbv can reduce on rewrite rules, with some limitations (e.g. simpl cannot reduce on rules which contain a match).
Also, regular unification can work with rewrite rules, as well as apply's unification mechanism in a limited manner (only if the pattern contains no match or projections).

On the other hand, some operations are not supported, such as declaring rules in sections and some interactions with modules.
Since rewrite rules may introduce untyped terms, which the VM and native reduction machines don't support (risk of segfault or code injection),
they are turned off when rewrite rules are enabled.
