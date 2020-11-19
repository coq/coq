Variants and the `match` construct
==================================

Variants
--------

.. cmd:: Variant @variant_definition {* with @variant_definition }

   .. insertprodn variant_definition variant_definition

   .. prodn::
      variant_definition ::= @ident_decl {* @binder } {? %| {* @binder } } {? : @type } := {? %| } {+| @constructor } {? @decl_notations }

   The :cmd:`Variant` command is similar to the :cmd:`Inductive` command, except
   that it disallows recursive definition of types (for instance, lists cannot
   be defined using :cmd:`Variant`). No induction scheme is generated for
   this variant, unless the :flag:`Nonrecursive Elimination Schemes` flag is on.

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(template)`, :attr:`universes(cumulative)`, and
   :attr:`private(matching)` attributes.

   .. exn:: The @natural th argument of @ident must be @ident in @type.
      :undocumented:

Private (matching) inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. attr:: private(matching)
   :name: private(matching); Private

   This attribute can be used to forbid the use of the :g:`match`
   construct on objects of this inductive type outside of the module
   where it is defined.  There is also a legacy syntax using the
   ``Private`` prefix (cf. :n:`@legacy_attr`).

   The main use case of private (matching) inductive types is to emulate
   quotient types / higher-order inductive types in projects such as
   the `HoTT library <https://github.com/HoTT/HoTT>`_.

.. example::

   .. coqtop:: all

      Module Foo.
      #[ private(matching) ] Inductive my_nat := my_O : my_nat | my_S : my_nat -> my_nat.
      Check (fun x : my_nat => match x with my_O => true | my_S _ => false end).
      End Foo.
      Import Foo.
      Fail Check (fun x : my_nat => match x with my_O => true | my_S _ => false end).

.. index:: match ... with ...

.. _match_term:

Definition by cases: match
--------------------------

Objects of inductive types can be destructured by a case-analysis
construction called *pattern matching* expression. A pattern matching
expression is used to analyze the structure of an inductive object and
to apply specific treatments accordingly.

.. insertprodn term_match pattern0

.. prodn::
   term_match ::= match {+, @case_item } {? return @term100 } with {? %| } {*| @eqn } end
   case_item ::= @term100 {? as @name } {? in @pattern }
   eqn ::= {+| {+, @pattern } } => @term
   pattern ::= @pattern10 : @term
   | @pattern10
   pattern10 ::= @pattern1 as @name
   | @pattern1 {* @pattern1 }
   | @ @qualid {* @pattern1 }
   pattern1 ::= @pattern0 % @scope_key
   | @pattern0
   pattern0 ::= @qualid
   | %{%| {* @qualid := @pattern } %|%}
   | _
   | ( {+| @pattern } )
   | @number
   | @string

Note that the :n:`@pattern ::= @pattern10 : @term` production
is not supported in :n:`match` patterns.  Trying to use it will give this error:

.. exn:: Casts are not supported in this pattern.
   :undocumented:


This paragraph describes the basic form of pattern matching. See
Section :ref:`Mult-match` and Chapter :ref:`extendedpatternmatching` for the description
of the general form. The basic form of pattern matching is characterized
by a single :n:`@case_item` expression, an :n:`@eqn` restricted to a
single :n:`@pattern` and :n:`@pattern` restricted to the form
:n:`@qualid {* @ident}`.

The expression
:n:`match @term {? return @term100 } with {+| @pattern__i => @term__i } end` denotes a
*pattern matching* over the term :n:`@term` (expected to be
of an inductive type :math:`I`). The :n:`@term__i`
are the *branches* of the pattern matching
expression. Each :n:`@pattern__i` has the form :n:`@qualid @ident`
where :n:`@qualid` must denote a constructor. There should be
exactly one branch for every constructor of :math:`I`.

The :n:`return @term100` clause gives the type returned by the whole match
expression. There are several cases. In the *non dependent* case, all
branches have the same type, and the :n:`return @term100` specifies that type.
In this case, :n:`return @term100` can usually be omitted as it can be
inferred from the type of the branches [1]_.

In the *dependent* case, there are three subcases. In the first subcase,
the type in each branch may depend on the exact value being matched in
the branch. In this case, the whole pattern matching itself depends on
the term being matched. This dependency of the term being matched in the
return type is expressed with an :n:`@ident` clause where :n:`@ident`
is dependent in the return type. For instance, in the following example:

.. coqtop:: in

   Inductive bool : Type := true : bool | false : bool.
   Inductive eq (A:Type) (x:A) : A -> Prop := eq_refl : eq A x x.
   Inductive or (A:Prop) (B:Prop) : Prop :=
     | or_introl : A -> or A B
     | or_intror : B -> or A B.

   Definition bool_case (b:bool) : or (eq bool b true) (eq bool b false) :=
     match b as x return or (eq bool x true) (eq bool x false) with
     | true => or_introl (eq bool true true) (eq bool true false) (eq_refl bool true)
     | false => or_intror (eq bool false true) (eq bool false false) (eq_refl bool false)
     end.

the branches have respective types ":g:`or (eq bool true true) (eq bool true false)`"
and ":g:`or (eq bool false true) (eq bool false false)`" while the whole
pattern matching expression has type ":g:`or (eq bool b true) (eq bool b false)`",
the identifier :g:`b` being used to represent the dependency.

.. note::

   When the term being matched is a variable, the ``as`` clause can be
   omitted and the term being matched can serve itself as binding name in
   the return type. For instance, the following alternative definition is
   accepted and has the same meaning as the previous one.

   .. coqtop:: none

      Reset bool_case.

   .. coqtop:: in

      Definition bool_case (b:bool) : or (eq bool b true) (eq bool b false) :=
      match b return or (eq bool b true) (eq bool b false) with
      | true => or_introl (eq bool true true) (eq bool true false) (eq_refl bool true)
      | false => or_intror (eq bool false true) (eq bool false false) (eq_refl bool false)
      end.

The second subcase is only relevant for annotated inductive types such
as the equality predicate (see Section :ref:`coq-equality`),
the order predicate on natural numbers or the type of lists of a given
length (see Section :ref:`matching-dependent`). In this configuration, the
type of each branch can depend on the type dependencies specific to the
branch and the whole pattern matching expression has a type determined
by the specific dependencies in the type of the term being matched. This
dependency of the return type in the annotations of the inductive type
is expressed with a clause in the form
:n:`in @qualid {+ _ } {+ @pattern }`, where

-  :n:`@qualid` is the inductive type of the term being matched;

-  the holes :n:`_` match the parameters of the inductive type: the
   return type is not dependent on them.

-  each :n:`@pattern` matches the annotations of the
   inductive type: the return type is dependent on them

-  in the basic case which we describe below, each :n:`@pattern`
   is a name :n:`@ident`; see :ref:`match-in-patterns` for the
   general case

For instance, in the following example:

.. coqtop:: in

   Definition eq_sym (A:Type) (x y:A) (H:eq A x y) : eq A y x :=
   match H in eq _ _ z return eq A z x with
   | eq_refl _ _ => eq_refl A x
   end.

the type of the branch is :g:`eq A x x` because the third argument of
:g:`eq` is :g:`x` in the type of the pattern :g:`eq_refl`. On the contrary, the
type of the whole pattern matching expression has type :g:`eq A y x` because the
third argument of eq is y in the type of H. This dependency of the case analysis
in the third argument of :g:`eq` is expressed by the identifier :g:`z` in the
return type.

Finally, the third subcase is a combination of the first and second
subcase. In particular, it only applies to pattern matching on terms in
a type with annotations. For this third subcase, both the clauses ``as`` and
``in`` are available.

There are specific notations for case analysis on types with one or two
constructors: ``if … then … else …`` and ``let (…,…) := … in …`` (see
Sections :ref:`if-then-else` and :ref:`irrefutable-patterns`).

.. [1]
   Except if the inductive type is empty in which case there is no
   equation that can be used to infer the return type.
