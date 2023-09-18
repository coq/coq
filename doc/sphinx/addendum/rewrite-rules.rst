.. _rewrite_rules:

User-defined rewrite rules
==========================

.. warning::

   The status of rewrite rules is highly experimental.

   In particular, ill-typed rewrite rules will lead to mistyped expressions,
   and manipulating these will most often result in anomalies.
   Furthermore, some parts of Coq like conversion checking through bytecode or native code
   compilation currently do not understand rewrite rules.


Declaring symbols
-----------------

Rewrite rules operate on symbols, which are their own kind of constants.

.. cmd:: {| Symbol | Symbols } {| {+ ( @assumpt ) } | @assumpt }
   :name: Symbol; Symbols

   Symbols are declared in the same way as axioms, by giving their type and using the keyword ``Symbol``.

   .. coqtop:: all

      Symbol pplus : nat -> nat -> nat.
      Notation "a ++ b" := (pplus a b).

Declaring rules
---------------

Rewrite rules have two parts named pattern (lhs) and production (rhs).
When a rule is applied, the term is matched against the pattern, subterms aligned with pattern holes are collected
and substitued into the production which is returned.

.. cmd:: Rewrite {| Rule | Rules } @ident := @rewrite_rule {* with @rewrite_rule }
  :name: Rewrite; Rule; Rules

   Rewrite rules are declared in blocks, which bear a name.

  .. prodn::
     rewrite_rule ::= @term ==> @term


  .. coqtop:: all

     Rewrite Rule pplus_rewrite :=
          ?n ++ 0 ==> ?n
     with ?n ++ S ?m ==> S (?n ++ ?m)
     with 0 ++ ?n ==> ?n
     with S ?n ++ ?m ==> S (?n ++ ?m).

Pattern syntax
--------------

Patterns are read from a subpart of terms, with the following syntax :

  .. prodn::
     pat ::= @qualid {? @univ_annot }
     | @pat {+ @arg_pat }
     | @pat .( @qualid {? @univ_annot } )
     | match @pat {? as @name in @qualid {* {| @name | _ } } } {? return @arg_pat } with {? %| } {*| @qualid {* {| @name | _ } } => @arg_pat } end
     | fun ({+ @name } {? : @arg_pat}) => @arg_pat
     | forall ({+ @name } {? : @arg_pat}), @arg_pat
     arg_pat ::= ? @name | _ | @pat

where :n:`@qualid {? @univ_annot }` can refer to symbols, inductives and constructors, but not arbitrary constants.

Equivalently, we can see a pattern as a pair of a rigid head and a list of eliminations :

  .. prodn::
     head_pat ::= @qualid {? @univ_annot }
     | fun ({+ @name } {? : @arg_pat}) => @arg_pat
     | forall ({+ @name } {? : @arg_pat}), @arg_pat
     elimination ::= <> {+ @pat }
     | <> .( @qualid {? @univ_annot } )
     | match <> {? as @name in @qualid {* {| @name | _ } } } {? return @arg_pat } with {*| @qualid {* {| @name | _ } } => @arg_pat } end
     pat ::= @head_pat {* @elimination }
     arg_pat ::= ? @name | _ | @pat

To be a valid pattern, it also must have a symbol as its head pattern, since the mechanism to trigger rewrite rules needs a symbol.

Productions
-----------

Productions are regular terms, which can also refer to matched holes in the pattern, through the :n:`? @name` syntax.


Higher-order pattern holes
--------------------------

Pattern production lambda, prod and match introduce new variables in the context which need to be taken into account in the production.
To this end, the user can add what each new variable should become in the production, using the syntax :n:`? @name @%{ {+; @name := @term } %}`.
Note that if in the production, the context was extended with a variable bearing the same name, this explicit substitution is inferred automatically (like for existential variable instantiations).


   .. coqtop:: all

      Symbol raise : forall (A : Type), A.
      Rewrite Rule raise_nat :=
         match raise nat as n return ?P with 0 => _ | S _ => _ end ==> raise ?P@{n := raise nat}.

      Symbol id : forall (A : Type), A -> A.
      Rewrite Rule id_rew :=
         id (forall (x : ?A), ?P) ?f ==> fun (x : ?A) => id ?P (?f x).

Rewrite rules, type preservation, confluence and termination
------------------------------------------------------------

Currently, rewrite rules are completely untyped. This means that the types of the production
and of the pattern are not checked (it is not even completely clear what the type of a pattern is).
This also means that reduction using a rewrite rule have no reason to preserve types, and even welltypedness at all.
The responsibility of ensuring type preservation falls on the user entirely.

Similarly, neither confluence nor termination are checked by the compiler.

There are future plans to add a check on confluence using the triangle criterion :cite:`TotR21` and a check on type preservation.

Level of support
----------------

Rewrite rules have been integrated into the kernel and the most used parts of the upper layers.
Notably, reduction machines simpl, cbn and cbv can reduce on rewrite rules, with some limitations (e.g. simpl cannot reduce on rules which contain a match).
Also, regular unification can work with rewrite rules, as well as apply's unification mechanism in a limited manner (only if the pattern has no match or projections).

On the other hand, some operations are not supported, such as declaring rules in sections and some interactions with modules.
The VM and native reductions also do not understand rewrite rules.
