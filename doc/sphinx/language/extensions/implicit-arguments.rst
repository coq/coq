.. _ImplicitArguments:

Implicit arguments
------------------

An implicit argument of a function is an argument which can be
inferred from contextual knowledge. There are different kinds of
implicit arguments that can be considered implicit in different ways.
There are also various commands to control the setting or the
inference of implicit arguments.


The different kinds of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Implicit arguments inferable from the knowledge of other arguments of a function
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

The first kind of implicit arguments covers the arguments that are
inferable from the knowledge of the type of other arguments of the
function, or of the type of the surrounding context of the
application. Especially, such implicit arguments correspond to
parameters dependent in the type of the function. Typical implicit
arguments are the type arguments in polymorphic functions. There are
several kinds of such implicit arguments.

**Strict Implicit Arguments**

An implicit argument can be either strict or non strict. An implicit
argument is said to be *strict* if, whatever the other arguments of the
function are, it is still inferable from the type of some other
argument. Technically, an implicit argument is strict if it
corresponds to a parameter which is not applied to a variable which
itself is another parameter of the function (since this parameter may
erase its arguments), not in the body of a match, and not itself
applied or matched against patterns (since the original form of the
argument can be lost by reduction).

For instance, the first argument of
::

  cons: forall A:Set, A -> list A -> list A

in module ``List.v`` is strict because :g:`list` is an inductive type and :g:`A`
will always be inferable from the type :g:`list A` of the third argument of
:g:`cons`. Also, the first argument of :g:`cons` is strict with respect to the second one,
since the first argument is exactly the type of the second argument.
On the contrary, the second argument of a term of type
::

  forall P:nat->Prop, forall n:nat, P n -> ex nat P

is implicit but not strict, since it can only be inferred from the
type :g:`P n` of the third argument and if :g:`P` is, e.g., :g:`fun _ => True`, it
reduces to an expression where ``n`` does not occur any longer. The first
argument :g:`P` is implicit but not strict either because it can only be
inferred from :g:`P n` and :g:`P` is not canonically inferable from an arbitrary
:g:`n` and the normal form of :g:`P n`. Consider, e.g., that :g:`n` is :math:`0` and the third
argument has type :g:`True`, then any :g:`P` of the form
::

  fun n => match n with 0 => True | _ => anything end

would be a solution of the inference problem.

**Contextual Implicit Arguments**

An implicit argument can be *contextual* or not. An implicit argument
is said *contextual* if it can be inferred only from the knowledge of
the type of the context of the current expression. For instance, the
only argument of::

  nil : forall A:Set, list A`

is contextual. Similarly, both arguments of a term of type::

  forall P:nat->Prop, forall n:nat, P n \/ n = 0

are contextual (moreover, :g:`n` is strict and :g:`P` is not).

**Reversible-Pattern Implicit Arguments**

There is another class of implicit arguments that can be reinferred
unambiguously if all the types of the remaining arguments are known.
This is the class of implicit arguments occurring in the type of
another argument in position of reversible pattern, which means it is
at the head of an application but applied only to uninstantiated
distinct variables. Such an implicit argument is called *reversible-
pattern implicit argument*. A typical example is the argument :g:`P` of
nat_rec in
::

  nat_rec : forall P : nat -> Set, P 0 ->
    (forall n : nat, P n -> P (S n)) -> forall x : nat, P x

(:g:`P` is reinferable by abstracting over :g:`n` in the type :g:`P n`).

See :ref:`controlling-rev-pattern-implicit-args` for the automatic declaration of reversible-pattern
implicit arguments.

Implicit arguments inferable by resolution
++++++++++++++++++++++++++++++++++++++++++

This corresponds to a class of non-dependent implicit arguments that
are solved based on the structure of their type only.


Maximal or non maximal insertion of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In case a function is partially applied, and the next argument to be
applied is an implicit argument, two disciplines are applicable. In
the first case, the function is considered to have no arguments
furtherly: one says that the implicit argument is not maximally
inserted. In the second case, the function is considered to be
implicitly applied to the implicit arguments it is waiting for: one
says that the implicit argument is maximally inserted.

Each implicit argument can be declared to be inserted maximally or non
maximally. In Coq, maximally-inserted implicit arguments are written between curly braces
"{ }" and non-maximally-inserted implicit arguments are written in square brackets "[ ]".

.. seealso:: :flag:`Maximal Implicit Insertion`

Trailing Implicit Arguments
+++++++++++++++++++++++++++

An implicit argument is considered trailing when all following arguments are declared
implicit. Trailing implicit arguments cannot be declared non maximally inserted,
otherwise they would never be inserted.

.. exn:: Argument @name is a trailing implicit, so it can't be declared non maximal. Please use %{ %} instead of [ ].

   For instance:

   .. coqtop:: all fail

      Fail Definition double [n] := n + n.


Casual use of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In a given expression, if it is clear that some argument of a function
can be inferred from the type of the other arguments, the user can
force the given argument to be guessed by replacing it by “_”. If
possible, the correct argument will be automatically generated.

.. exn:: Cannot infer a term for this placeholder.
   :name: Cannot infer a term for this placeholder. (Casual use of implicit arguments)

   |Coq| was not able to deduce an instantiation of a “_”.

.. _declare-implicit-args:

Declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In case one wants that some arguments of a given object (constant,
inductive types, constructors, assumptions, local or not) are always
inferred by |Coq|, one may declare once and for all which are the
expected implicit arguments of this object. There are two ways to do
this, *a priori* and *a posteriori*.


Implicit Argument Binders
+++++++++++++++++++++++++

.. insertprodn implicit_binders implicit_binders

.. prodn::
   implicit_binders ::= %{ {+ @name } {? : @type } %}
   | [ {+ @name } {? : @type } ]

In the first setting, one wants to explicitly give the implicit
arguments of a declared object as part of its definition. To do this,
one has to surround the bindings of implicit arguments by curly
braces or square braces:

.. coqtop:: all

   Definition id {A : Type} (x : A) : A := x.

This automatically declares the argument A of id as a maximally
inserted implicit argument. One can then do as-if the argument was
absent in every situation but still be able to specify it if needed:

.. coqtop:: all

   Definition compose {A B C} (g : B -> C) (f : A -> B) := fun x => g (f x).

   Goal forall A, compose id id = id (A:=A).

For non maximally inserted implicit arguments, use square brackets:

.. coqtop:: all

   Fixpoint map [A B : Type] (f : A -> B) (l : list A) : list B :=
     match l with
     | nil => nil
     | cons a t => cons (f a) (map f t)
     end.

   Print Implicit map.

The syntax is supported in all top-level definitions:
:cmd:`Definition`, :cmd:`Fixpoint`, :cmd:`Lemma` and so on. For (co-)inductive datatype
declarations, the semantics are the following: an inductive parameter
declared as an implicit argument need not be repeated in the inductive
definition and will become implicit for the inductive type and the constructors.
For example:

.. coqtop:: all

   Inductive list {A : Type} : Type :=
   | nil : list
   | cons : A -> list -> list.

   Print list.

One can always specify the parameter if it is not uniform using the
usual implicit arguments disambiguation syntax.

The syntax is also supported in internal binders. For instance, in the
following kinds of expressions, the type of each declaration present
in :token:`binders` can be bracketed to mark the declaration as
implicit:
:n:`fun (@ident:forall {* @binder }, @type) => @term`,
:n:`forall (@ident:forall {* @binder }, @type), @type`,
:n:`let @ident {* @binder } := @term in @term`,
:n:`fix @ident {* @binder } := @term in @term` and
:n:`cofix @ident {* @binder } := @term in @term`.
Here is an example:

.. coqtop:: all

   Axiom Ax :
     forall (f:forall {A} (a:A), A * A),
     let g {A} (x y:A) := (x,y) in
     f 0 = g 0 0.

.. warn:: Ignoring implicit binder declaration in unexpected position

   This is triggered when setting an argument implicit in an
   expression which does not correspond to the type of an assumption
   or to the body of a definition. Here is an example:

   .. coqtop:: all warn

      Definition f := forall {y}, y = 0.

.. warn:: Making shadowed name of implicit argument accessible by position

   This is triggered when two variables of same name are set implicit
   in the same block of binders, in which case the first occurrence is
   considered to be unnamed. Here is an example:

   .. coqtop:: all warn

      Check let g {x:nat} (H:x=x) {x} (H:x=x) := x in 0.


Declaring Implicit Arguments
++++++++++++++++++++++++++++



.. cmd:: Arguments @smart_qualid {* @argument_spec_block } {* , {* @more_implicits_block } } {? : {+, @arguments_modifier } }
   :name: Arguments

   .. insertprodn smart_qualid arguments_modifier

   .. prodn::
      smart_qualid ::= @qualid
      | @by_notation
      by_notation ::= @string {? % @scope }
      argument_spec_block ::= @argument_spec
      | /
      | &
      | ( {+ @argument_spec } ) {? % @scope }
      | [ {+ @argument_spec } ] {? % @scope }
      | %{ {+ @argument_spec } %} {? % @scope }
      argument_spec ::= {? ! } @name {? % @scope }
      more_implicits_block ::= @name
      | [ {+ @name } ]
      | %{ {+ @name } %}
      arguments_modifier ::= simpl nomatch
      | simpl never
      | default implicits
      | clear bidirectionality hint
      | clear implicits
      | clear scopes
      | clear scopes and implicits
      | clear implicits and scopes
      | rename
      | assert
      | extra scopes

   This command sets implicit arguments *a posteriori*,
   where the list of :n:`@name`\s is a prefix of the list of
   arguments of :n:`@smart_qualid`.  Arguments in square
   brackets are declared as implicit and arguments in curly brackets are declared as
   maximally inserted.

   After the command is issued, implicit arguments can and must be
   omitted in any expression that applies :token:`qualid`.

   This command supports the :attr:`local` and :attr:`global` attributes.
   Default behavior is to limit the effect to the current section but also to
   extend their effect outside the current module or library file.
   Applying :attr:`local` limits the effect of the command to the current module if
   it's not in a section.  Applying :attr:`global` within a section extends the
   effect outside the current sections and current module if the command occurs.

   A command containing :n:`@argument_spec_block & @argument_spec_block`
   provides :ref:`bidirectionality_hints`.

   Use the :n:`@more_implicits_block` to specify multiple implicit arguments declarations
   for names of constants, inductive types, constructors and lemmas that can only be
   applied to a fixed number of arguments (excluding, for instance,
   constants whose type is polymorphic).
   The longest applicable list of implicit arguments will be used to select which
   implicit arguments are inserted.
   For printing, the omitted arguments are the ones of the longest list of implicit
   arguments of the sequence.  See the example :ref:`here<example_more_implicits>`.

   The :n:`@arguments_modifier` values have various effects:

   * :n:`clear implicits` - clears implicit arguments
   * :n:`default implicits` - automatically determine the implicit arguments of the object.
     See :ref:`auto_decl_implicit_args`.
   * :n:`rename` - rename implicit arguments for the object
   * :n:`assert` - assert that the object has the expected number of arguments with the
     expected names.  See the example here: :ref:`renaming_implicit_arguments`.

.. exn:: The / modifier may only occur once.
   :undocumented:

.. exn:: The & modifier may only occur once.
   :undocumented:

.. example::

    .. coqtop:: reset all

       Inductive list (A : Type) : Type :=
       | nil : list A
       | cons : A -> list A -> list A.

       Check (cons nat 3 (nil nat)).

       Arguments cons [A] _ _.

       Arguments nil {A}.

       Check (cons 3 nil).

       Fixpoint map (A B : Type) (f : A -> B) (l : list A) : list B :=
         match l with nil => nil | cons a t => cons (f a) (map A B f t) end.

       Fixpoint length (A : Type) (l : list A) : nat :=
         match l with nil => 0 | cons _ m => S (length A m) end.

       Arguments map [A B] f l.

       Arguments length {A} l. (* A has to be maximally inserted *)

       Check (fun l:list (list nat) => map length l).

.. _example_more_implicits:

.. example:: Multiple implicit arguments with :n:`@more_implicits_block`

   .. coqtop:: all

       Arguments map [A B] f l, [A] B f l, A B f l.

       Check (fun l => map length l = map (list nat) nat length l).

.. note::
   Use the :cmd:`Print Implicit` command to see the implicit arguments
   of an object (see :ref:`displaying-implicit-args`).

.. _auto_decl_implicit_args:

Automatic declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The :n:`default implicits @arguments_modifier` clause tells |Coq| to automatically determine the
   implicit arguments of the object.

   Auto-detection is governed by flags specifying whether strict,
   contextual, or reversible-pattern implicit arguments must be
   considered or not (see :ref:`controlling-strict-implicit-args`, :ref:`controlling-contextual-implicit-args`,
   :ref:`controlling-rev-pattern-implicit-args` and also :ref:`controlling-insertion-implicit-args`).

.. example:: Default implicits

   .. coqtop:: reset all

       Inductive list (A:Set) : Set :=
       | nil : list A
       | cons : A -> list A -> list A.

       Arguments cons : default implicits.

       Print Implicit cons.

       Arguments nil : default implicits.

       Print Implicit nil.

       Set Contextual Implicit.

       Arguments nil : default implicits.

       Print Implicit nil.

The computation of implicit arguments takes account of the unfolding
of constants. For instance, the variable ``p`` below has type
``(Transitivity R)`` which is reducible to
``forall x,y:U, R x y -> forall z:U, R y z -> R x z``. As the variables ``x``, ``y`` and ``z``
appear strictly in the body of the type, they are implicit.

.. coqtop:: all

   Parameter X : Type.

   Definition Relation := X -> X -> Prop.

   Definition Transitivity (R:Relation) := forall x y:X, R x y -> forall z:X, R y z -> R x z.

   Parameters (R : Relation) (p : Transitivity R).

   Arguments p : default implicits.

   Print p.

   Print Implicit p.

   Parameters (a b c : X) (r1 : R a b) (r2 : R b c).

   Check (p r1 r2).


Mode for automatic declaration of implicit arguments
++++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Implicit Arguments

   This flag (off by default) allows to systematically declare implicit
   the arguments detectable as such. Auto-detection of implicit arguments is
   governed by flags controlling whether strict and contextual implicit
   arguments have to be considered or not.

.. _controlling-strict-implicit-args:

Controlling strict implicit arguments
+++++++++++++++++++++++++++++++++++++

.. flag:: Strict Implicit

   When the mode for automatic declaration of implicit arguments is on,
   the default is to automatically set implicit only the strict implicit
   arguments plus, for historical reasons, a small subset of the non-strict
   implicit arguments. To relax this constraint and to set
   implicit all non strict implicit arguments by default, you can turn this
   flag off.

.. flag:: Strongly Strict Implicit

   Use this flag (off by default) to capture exactly the strict implicit
   arguments and no more than the strict implicit arguments.

.. _controlling-contextual-implicit-args:

Controlling contextual implicit arguments
+++++++++++++++++++++++++++++++++++++++++

.. flag:: Contextual Implicit

   By default, |Coq| does not automatically set implicit the contextual
   implicit arguments. You can turn this flag on to tell |Coq| to also
   infer contextual implicit argument.

.. _controlling-rev-pattern-implicit-args:

Controlling reversible-pattern implicit arguments
+++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Reversible Pattern Implicit

   By default, |Coq| does not automatically set implicit the reversible-pattern
   implicit arguments. You can turn this flag on to tell |Coq| to also infer
   reversible-pattern implicit argument.

.. _controlling-insertion-implicit-args:

Controlling the insertion of implicit arguments not followed by explicit arguments
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Maximal Implicit Insertion

   Assuming the implicit argument mode is on, this flag (off by default)
   declares implicit arguments to be automatically inserted when a
   function is partially applied and the next argument of the function is
   an implicit one.

Combining manual declaration and automatic declaration
++++++++++++++++++++++++++++++++++++++++++++++++++++++

When some arguments are manually specified implicit with binders in a definition
and the automatic declaration mode in on, the manual implicit arguments are added to the
automatically declared ones.

In that case, and when the flag :flag:`Maximal Implicit Insertion` is set to off,
some trailing implicit arguments can be inferred to be non maximally inserted. In
this case, they are converted to maximally inserted ones.

.. example::

   .. coqtop:: all

      Set Implicit Arguments.
      Axiom eq0_le0 : forall (n : nat) (x : n = 0), n <= 0.
      Print Implicit eq0_le0.
      Axiom eq0_le0' : forall (n : nat) {x : n = 0}, n <= 0.
      Print Implicit eq0_le0'.


.. _explicit-applications:

Explicit applications
~~~~~~~~~~~~~~~~~~~~~

In presence of non-strict or contextual arguments, or in presence of
partial applications, the synthesis of implicit arguments may fail, so
one may have to explicitly give certain implicit arguments of an
application. Use the :n:`(@ident := @term)` form of :token:`arg` to do so,
where :token:`ident` is the name of the implicit argument and :token:`term`
is its corresponding explicit term. Alternatively, one can deactivate
the hiding of implicit arguments for a single function application using the
:n:`@ @qualid {? @univ_annot } {* @term1 }` form of :token:`term10`.

.. example:: Syntax for explicitly giving implicit arguments (continued)

    .. coqtop:: all

       Check (p r1 (z:=c)).

       Check (p (x:=a) (y:=b) r1 (z:=c) r2).


.. _renaming_implicit_arguments:

Renaming implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. example:: (continued)  Renaming implicit arguments

   .. coqtop:: all

      Arguments p [s t] _ [u] _: rename.

      Check (p r1 (u:=c)).

      Check (p (s:=a) (t:=b) r1 (u:=c) r2).

      Fail Arguments p [s t] _ [w] _ : assert.

.. _displaying-implicit-args:

Displaying implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Implicit @smart_qualid

   Displays the implicit arguments associated with an object,
   identifying which arguments are applied maximally or not.


Displaying implicit arguments when pretty-printing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Implicit

   By default, the basic pretty-printing rules hide the inferrable implicit
   arguments of an application. Turn this flag on to force printing all
   implicit arguments.

.. flag:: Printing Implicit Defensive

   By default, the basic pretty-printing rules display implicit
   arguments that are not detected as strict implicit arguments. This
   “defensive” mode can quickly make the display cumbersome so this can
   be deactivated by turning this flag off.

.. seealso:: :flag:`Printing All`.

Interaction with subtyping
~~~~~~~~~~~~~~~~~~~~~~~~~~

When an implicit argument can be inferred from the type of more than
one of the other arguments, then only the type of the first of these
arguments is taken into account, and not an upper type of all of them.
As a consequence, the inference of the implicit argument of “=” fails
in

.. coqtop:: all

   Fail Check nat = Prop.

but succeeds in

.. coqtop:: all

   Check Prop = nat.


Deactivation of implicit arguments for parsing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Parsing Explicit

   Turning this flag on (it is off by default) deactivates the use of implicit arguments.

   In this case, all arguments of constants, inductive types,
   constructors, etc, including the arguments declared as implicit, have
   to be given as if no arguments were implicit. By symmetry, this also
   affects printing.

.. _canonical-structure-declaration:

Canonical structures
~~~~~~~~~~~~~~~~~~~~

A canonical structure is an instance of a record/structure type that
can be used to solve unification problems involving a projection
applied to an unknown structure instance (an implicit argument) and a
value. The complete documentation of canonical structures can be found
in :ref:`canonicalstructures`; here only a simple example is given.

.. cmd:: Canonical {? Structure } @smart_qualid
         Canonical {? Structure } @ident_decl @def_body
   :name: Canonical Structure; _

   The first form of this command declares an existing :n:`@smart_qualid` as a
   canonical instance of a structure (a record).

   The second form defines a new constant as if the :cmd:`Definition` command
   had been used, then declares it as a canonical instance as if the first
   form had been used on the defined object.

   This command supports the :attr:`local` attribute.  When used, the
   structure is canonical only within the :cmd:`Section` containing it.

   Assume that :token:`qualid` denotes an object ``(Build_struct`` |c_1| … |c_n| ``)`` in the
   structure :g:`struct` of which the fields are |x_1|, …, |x_n|.
   Then, each time an equation of the form ``(``\ |x_i| ``_)`` |eq_beta_delta_iota_zeta| |c_i| has to be
   solved during the type checking process, :token:`qualid` is used as a solution.
   Otherwise said, :token:`qualid` is canonically used to extend the field |c_i|
   into a complete structure built on |c_i|.

   Canonical structures are particularly useful when mixed with coercions
   and strict implicit arguments.

   .. example::

      Here is an example.

      .. coqtop:: all

         Require Import Relations.

         Require Import EqNat.

         Set Implicit Arguments.

         Unset Strict Implicit.

         Structure Setoid : Type := {Carrier :> Set; Equal : relation Carrier;
                                     Prf_equiv : equivalence Carrier Equal}.

         Definition is_law (A B:Setoid) (f:A -> B) := forall x y:A, Equal x y -> Equal (f x) (f y).

         Axiom eq_nat_equiv : equivalence nat eq_nat.

         Definition nat_setoid : Setoid := Build_Setoid eq_nat_equiv.

         Canonical nat_setoid.

      Thanks to :g:`nat_setoid` declared as canonical, the implicit arguments :g:`A`
      and :g:`B` can be synthesized in the next statement.

      .. coqtop:: all abort

         Lemma is_law_S : is_law S.

   .. note::
      If a same field occurs in several canonical structures, then
      only the structure declared first as canonical is considered.

   .. attr:: canonical(false)

      To prevent a field from being involved in the inference of
      canonical instances, its declaration can be annotated with the
      :attr:`canonical(false)` attribute (cf. the syntax of
      :n:`@record_field`).

      .. example::

         For instance, when declaring the :g:`Setoid` structure above, the
         :g:`Prf_equiv` field declaration could be written as follows.

         .. coqdoc::

            #[canonical(false)] Prf_equiv : equivalence Carrier Equal

      See :ref:`canonicalstructures` for a more realistic example.

.. attr:: canonical

   This attribute can decorate a :cmd:`Definition` or :cmd:`Let` command.
   It is equivalent to having a :cmd:`Canonical Structure` declaration just
   after the command.

.. cmd:: Print Canonical Projections {* @smart_qualid }

   This displays the list of global names that are components of some
   canonical structure. For each of them, the canonical structure of
   which it is a projection is indicated. If constants are given as
   its arguments, only the unification rules that involve or are
   synthesized from simultaneously all given constants will be shown.

   .. example::

      For instance, the above example gives the following output:

      .. coqtop:: all

         Print Canonical Projections.

      .. coqtop:: all

         Print Canonical Projections nat.

      .. note::

         The last line in the first example would not show up if the
         corresponding projection (namely :g:`Prf_equiv`) were annotated as not
         canonical, as described above.

Implicit types of variables
~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is possible to bind variable names to a given type (e.g. in a
development using arithmetic, it may be convenient to bind the names :g:`n`
or :g:`m` to the type :g:`nat` of natural numbers).

.. cmd:: Implicit {| Type | Types } @reserv_list
   :name: Implicit Type; Implicit Types

   .. insertprodn reserv_list simple_reserv

   .. prodn::
      reserv_list ::= {+ ( @simple_reserv ) }
      | @simple_reserv
      simple_reserv ::= {+ @ident } : @type

   Sets the type of bound
   variables starting with :token:`ident` (either :token:`ident` itself or
   :token:`ident` followed by one or more single quotes, underscore or
   digits) to :token:`type` (unless the bound variable is already declared
   with an explicit type, in which case, that type will be used).

.. example::

    .. coqtop:: all

       Require Import List.

       Implicit Types m n : nat.

       Lemma cons_inj_nat : forall m n l, n :: l = m :: l -> n = m.
       Proof. intros m n. Abort.

       Lemma cons_inj_bool : forall (m n:bool) l, n :: l = m :: l -> n = m.
       Abort.

.. flag:: Printing Use Implicit Types

  By default, the type of bound variables is not printed when
  the variable name is associated to an implicit type which matches the
  actual type of the variable. This feature can be deactivated by
  turning this flag off.

.. _implicit-generalization:

Implicit generalization
~~~~~~~~~~~~~~~~~~~~~~~

.. index:: `{ }
.. index:: `[ ]
.. index:: `( )
.. index:: `{! }
.. index:: `[! ]
.. index:: `(! )

.. insertprodn generalizing_binder typeclass_constraint

.. prodn::
   generalizing_binder ::= `( {+, @typeclass_constraint } )
   | `%{ {+, @typeclass_constraint } %}
   | `[ {+, @typeclass_constraint } ]
   typeclass_constraint ::= {? ! } @term
   | %{ @name %} : {? ! } @term
   | @name : {? ! } @term


Implicit generalization is an automatic elaboration of a statement
with free variables into a closed statement where these variables are
quantified explicitly.  Use the :cmd:`Generalizable` command to designate
which variables should be generalized.

It is activated for a binder by prefixing a \`, and for terms by
surrounding it with \`{ }, or \`[ ] or \`( ).

Terms surrounded by \`{ } introduce their free variables as maximally
inserted implicit arguments, terms surrounded by \`[ ] introduce them as
non maximally inserted implicit arguments and terms surrounded by \`( )
introduce them as explicit arguments.

Generalizing binders always introduce their free variables as
maximally inserted implicit arguments. The binder itself introduces
its argument as usual.

In the following statement, ``A`` and ``y`` are automatically
generalized, ``A`` is implicit and ``x``, ``y`` and the anonymous
equality argument are explicit.

.. coqtop:: all reset

   Generalizable All Variables.

   Definition sym `(x:A) : `(x = y -> y = x) := fun _ p => eq_sym p.

   Print sym.

Dually to normal binders, the name is optional but the type is required:

.. coqtop:: all

   Check (forall `{x = y :> A}, y = x).

When generalizing a binder whose type is a typeclass, its own class
arguments are omitted from the syntax and are generalized using
automatic names, without instance search. Other arguments are also
generalized unless provided. This produces a fully general statement.
this behaviour may be disabled by prefixing the type with a ``!`` or
by forcing the typeclass name to be an explicit application using
``@`` (however the later ignores implicit argument information).

.. coqtop:: all

   Class Op (A:Type) := op : A -> A -> A.

   Class Commutative (A:Type) `(Op A) := commutative : forall x y, op x y = op y x.
   Instance nat_op : Op nat := plus.

   Set Printing Implicit.
   Check (forall `{Commutative }, True).
   Check (forall `{Commutative nat}, True).
   Fail Check (forall `{Commutative nat _}, True).
   Fail Check (forall `{!Commutative nat}, True).
   Arguments Commutative _ {_}.
   Check (forall `{!Commutative nat}, True).
   Check (forall `{@Commutative nat plus}, True).

Multiple binders can be merged using ``,`` as a separator:

.. coqtop:: all

   Check (forall `{Commutative A, Hnat : !Commutative nat}, True).

.. cmd:: Generalizable {| {| Variable | Variables } {+ @ident } | All Variables | No Variables }

   Controls the set of generalizable identifiers.  By default, no variables are
   generalizable.

   This command supports the :attr:`global` attribute.

   The :n:`{| Variable | Variables } {+ @ident }` form allows generalization of only the given :n:`@ident`\s.
   Using this command multiple times adds to the allowed identifiers.  The other forms clear
   the list of :n:`@ident`\s.

   The :n:`All Variables` form generalizes all free variables in
   the context that appear under a
   generalization delimiter. This may result in confusing errors in case
   of typos. In such cases, the context will probably contain some
   unexpected generalized variables.

   The :n:`No Variables` form disables implicit generalization entirely.  This is
   the default behavior (before any :cmd:`Generalizable` command has been entered).
