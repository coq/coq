.. _ImplicitArguments:

Implicit arguments
------------------

An :gdef:`implicit argument` of a function is an argument which can be
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

An implicit argument can be either strict or non-strict. An implicit
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
is said to be *contextual* if it can be inferred only from the knowledge of
the type of the context of the current expression. For instance, the
only argument of::

  nil : forall A:Set, list A

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


Maximal and non-maximal insertion of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When a function is partially applied and the next argument to
apply is an implicit argument, the application can be interpreted in two ways.
If the next argument is declared as *maximally inserted*, the partial
application will include that argument.  Otherwise, the argument is
*non-maximally inserted* and the partial application will not include that argument.

Each implicit argument can be declared to be inserted maximally or non
maximally. In Rocq, maximally inserted implicit arguments are written between curly braces
"{ }" and non-maximally inserted implicit arguments are written in square brackets "[ ]".

.. seealso:: :flag:`Maximal Implicit Insertion`

Trailing Implicit Arguments
+++++++++++++++++++++++++++

An implicit argument is considered *trailing* when all following arguments are
implicit. Trailing implicit arguments must be declared as maximally inserted;
otherwise they would never be inserted.

.. exn:: Argument @name is a trailing implicit, so it can't be declared non maximal. Please use %{ %} instead of [ ].

   For instance:

   .. rocqtop:: all fail

      Fail Definition double [n] := n + n.


Casual use of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If an argument of a function application can be inferred from the type
of the other arguments, the user can force inference of the argument
by replacing it with `_`.

.. exn:: Cannot infer a term for this placeholder.
   :name: Cannot infer a term for this placeholder. (Casual use of implicit arguments)

   Rocq was not able to deduce an instantiation of a “_”.

.. _declare-implicit-args:

Declaration of implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Implicit arguments can be declared when a function is declared or
afterwards, using the :cmd:`Arguments` command.

Implicit Argument Binders
+++++++++++++++++++++++++

.. insertprodn implicit_binders implicit_binders

.. prodn::
   implicit_binders ::= %{ {+ @name } {? : @type } %}
   | [ {+ @name } {? : @type } ]

In the context of a function definition, these forms specify that
:token:`name` is an implicit argument.  The first form, with curly
braces, makes :token:`name` a maximally inserted implicit argument.  The second
form, with square brackets, makes :token:`name` a non-maximally inserted implicit argument.

For example:

.. rocqtop:: all

   Definition id {A : Type} (x : A) : A := x.

declares the argument `A` of `id` as a maximally
inserted implicit argument. `A` may be omitted
in applications of `id` but may be specified if needed:

.. rocqtop:: all abort

   Definition compose {A B C} (g : B -> C) (f : A -> B) := fun x => g (f x).

   Goal forall A, compose id id = id (A:=A).

For non-maximally inserted implicit arguments, use square brackets:

.. rocqtop:: all

   Fixpoint map [A B : Type] (f : A -> B) (l : list A) : list B :=
     match l with
     | nil => nil
     | cons a t => cons (f a) (map f t)
     end.

   Print Implicit map.

For (co)inductive datatype
declarations, the semantics are the following: an inductive parameter
declared as an implicit argument need not be repeated in the inductive
definition and will become implicit for the inductive type and the constructors.
For example:

.. rocqtop:: all

   Inductive list {A : Type} : Type :=
   | nil : list
   | cons : A -> list -> list.

   Print list.

One can always specify the parameter if it is not uniform using the
usual implicit arguments disambiguation syntax.

The syntax is also supported in internal binders. For instance, in the
following kinds of expressions, the type of each declaration present
in :n:`{* @binder }` can be bracketed to mark the declaration as
implicit:

* :n:`fun (@ident:forall {* @binder }, @type) => @term`,
* :n:`forall (@ident:forall {* @binder }, @type), @type`,
* :n:`let @ident {* @binder } := @term in @term`,
* :n:`fix @ident {* @binder } := @term in @term` and
* :n:`cofix @ident {* @binder } := @term in @term`.

Here is an example:

.. rocqtop:: all

   Axiom Ax :
     forall (f:forall {A} (a:A), A * A),
     let g {A} (x y:A) := (x,y) in
     f 0 = g 0 0.

.. warn:: Ignoring implicit binder declaration in unexpected position

   This is triggered when setting an argument implicit in an
   expression which does not correspond to the type of an assumption
   or to the :term:`body` of a definition. Here is an example:

   .. rocqtop:: all warn

      Definition f := forall {y}, y = 0.

.. warn:: Making shadowed name of implicit argument accessible by position

   This is triggered when two variables of same name are set implicit
   in the same block of binders, in which case the first occurrence is
   considered to be unnamed. Here is an example:

   .. rocqtop:: all warn

      Check let g {x:nat} (H:x=x) {x} (H:x=x) := x in 0.

Mode for automatic declaration of implicit arguments
++++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Implicit Arguments

   This :term:`flag` (off by default) allows to systematically declare implicit
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
   implicit all non-strict implicit arguments by default, you can turn this
   :term:`flag` off.

.. flag:: Strongly Strict Implicit

   Use this :term:`flag` (off by default) to capture exactly the strict implicit
   arguments and no more than the strict implicit arguments.

.. _controlling-contextual-implicit-args:

Controlling contextual implicit arguments
+++++++++++++++++++++++++++++++++++++++++

.. flag:: Contextual Implicit

   By default, Rocq does not automatically set implicit the contextual
   implicit arguments. You can turn this :term:`flag` on to tell Rocq to also
   infer contextual implicit argument.

.. _controlling-rev-pattern-implicit-args:

Controlling reversible-pattern implicit arguments
+++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Reversible Pattern Implicit

   By default, Rocq does not automatically set implicit the reversible-pattern
   implicit arguments. You can turn this :term:`flag` on to tell Rocq to also infer
   reversible-pattern implicit argument.

.. _controlling-insertion-implicit-args:

Controlling the insertion of implicit arguments not followed by explicit arguments
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Maximal Implicit Insertion

   Assuming the implicit argument mode is on, this :term:`flag` (off by default)
   declares implicit arguments to be automatically inserted when a
   function is partially applied and the next argument of the function is
   an implicit one.

Combining manual declaration and automatic declaration
++++++++++++++++++++++++++++++++++++++++++++++++++++++

When some arguments are manually specified implicit with binders in a definition
and the automatic declaration mode in on, the manual implicit arguments are added to the
automatically declared ones.

In that case, and when the flag :flag:`Maximal Implicit Insertion` is set to off,
some trailing implicit arguments can be inferred to be non-maximally inserted. In
this case, they are converted to maximally inserted ones.

.. example::

   .. rocqtop:: all

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
application.

To instantiate a dependent implicit argument, use the :n:`(@ident := @term)` form of :token:`arg`,
where :token:`ident` is the name of the implicit argument and :token:`term`
is its corresponding explicit term.

To instantiate a non-dependent implicit argument, use the :n:`(@natural := @term)` form of :token:`arg`,
where :token:`natural` is the index of the implicit argument among all
non-dependent arguments of the function (implicit or not, and starting
from 1) and :token:`term` is its corresponding explicit term.

Alternatively, one can deactivate
the hiding of implicit arguments for a single function application using the
:n:`@@qualid_annotated {+ @term1 }` form of :token:`term_application`.

.. example:: Syntax for explicitly giving implicit arguments (continued)

    .. rocqtop:: all

       Parameter X : Type.
       Definition Relation := X -> X -> Prop.
       Definition Transitivity (R:Relation) := forall x y:X, R x y -> forall z:X, R y z -> R x z.
       Parameters (R : Relation) (p : Transitivity R).
       Arguments p : default implicits.
       Print Implicit p.
       Parameters (a b c : X) (r1 : R a b) (r2 : R b c).
       Check (p r1 (z:=c)).

       Check (p (x:=a) (y:=b) r1 (z:=c) r2).

.. exn:: Wrong argument name
   :undocumented:

.. exn:: Wrong argument position
   :undocumented:

.. exn:: Argument at position @natural is mentioned more than once
   :undocumented:

.. exn:: Arguments given by name or position not supported in explicit mode
   :undocumented:

.. exn:: Not enough non implicit arguments to accept the argument bound to @ident
   :undocumented:

.. exn:: Not enough non implicit arguments to accept the argument bound to @natural
   :undocumented:

.. _displaying-implicit-args:

Displaying implicit arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Implicit @reference

   Displays the implicit arguments associated with an object,
   identifying which arguments are applied maximally or not.


Displaying implicit arguments when pretty-printing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Implicit

   By default, the basic pretty-printing rules hide the inferable implicit
   arguments of an application. Turn this :term:`flag` on to force printing all
   implicit arguments.

.. flag:: Printing Implicit Defensive

   By default, the basic pretty-printing rules display implicit
   arguments that are not detected as strict implicit arguments. This
   “defensive” mode can quickly make the display cumbersome so this can
   be deactivated by turning this :term:`flag` off.

.. seealso:: :flag:`Printing All`.

Interaction with subtyping
~~~~~~~~~~~~~~~~~~~~~~~~~~

When an implicit argument can be inferred from the type of more than
one of the other arguments, then only the type of the first of these
arguments is taken into account, and not an upper type of all of them.
As a consequence, the inference of the implicit argument of “=” fails
in

.. rocqtop:: all

   Fail Check nat = Prop.

but succeeds in

.. rocqtop:: all

   Check Prop = nat.

.. _deactivation-of-implicit-arguments:

Deactivation of implicit arguments for parsing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. insertprodn term_explicit term_explicit

.. prodn::
   term_explicit ::= @ @qualid_annotated

This syntax can be used to disable implicit arguments for a single
function.

.. example::

   The function `id` has one implicit argument and one explicit
   argument.

   .. rocqtop:: all reset

      Check (id 0).
      Definition id' := @id.

   The function `id'` has no implicit argument.

   .. rocqtop:: all

      Check (id' nat 0).

.. flag:: Parsing Explicit

   Turning this :term:`flag` on (it is off by default) deactivates the use of implicit arguments.

   In this case, all arguments of :term:`constants <constant>`, inductive types,
   constructors, etc, including the arguments declared as implicit, have
   to be given as if no arguments were implicit. By symmetry, this also
   affects printing.

.. example::

   We can reproduce the example above using the :flag:`Parsing
   Explicit` flag:

   .. rocqtop:: all reset

      Set Parsing Explicit.
      Definition id' := id.
      Unset Parsing Explicit.
      Check (id 1).
      Check (id' nat 1).

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

    .. rocqtop:: all

       Require Import ListDef.

       Implicit Types m n : nat.

       Lemma cons_inj_nat : forall m n l, n :: l = m :: l -> n = m.
       Proof. intros m n. Abort.

       Lemma cons_inj_bool : forall (m n:bool) l, n :: l = m :: l -> n = m.
       Abort.

.. flag:: Printing Use Implicit Types

  By default, the type of bound variables is not printed when
  the variable name is associated with an implicit type which matches the
  actual type of the variable. This feature can be deactivated by
  turning this :term:`flag` off.

.. _implicit-generalization:

Implicit generalization
~~~~~~~~~~~~~~~~~~~~~~~

.. index:: `{ }
.. index:: `[ ]
.. index:: `( )
.. index:: `{! }
.. index:: `[! ]
.. index:: `(! )

.. insertprodn generalizing_binder term_generalizing

.. prodn::
   generalizing_binder ::= `( {+, @typeclass_constraint } )
   | `%{ {+, @typeclass_constraint } %}
   | `[ {+, @typeclass_constraint } ]
   typeclass_constraint ::= {? ! } @term
   | %{ @name %} : {? ! } @term
   | @name : {? ! } @term
   term_generalizing ::= `%{ @term %}
   | `( @term )

Implicit generalization is an automatic elaboration of a statement
with free variables into a closed statement where these variables are
quantified explicitly.  Use the :cmd:`Generalizable` command to designate
which variables should be generalized.

It is activated within a binder by prefixing it with \`, and for terms by
surrounding it with \`{ }, or \`[ ] or \`( ).

Terms surrounded by \`{ } introduce their free variables as maximally
inserted implicit arguments, terms surrounded by \`[ ] introduce them as
non-maximally inserted implicit arguments and terms surrounded by \`( )
introduce them as explicit arguments.

Generalizing binders always introduce their free variables as
maximally inserted implicit arguments. The binder itself introduces
its argument as usual.

In the following statement, ``A`` and ``y`` are automatically
generalized, ``A`` is implicit and ``x``, ``y`` and the anonymous
equality argument are explicit.

.. rocqtop:: all reset

   Generalizable All Variables.

   Definition sym `(x:A) : `(x = y -> y = x) := fun _ p => eq_sym p.

   Print sym.

Dually to normal binders, the name is optional but the type is required:

.. rocqtop:: all

   Check (forall `{x = y :> A}, y = x).

When generalizing a binder whose type is a typeclass, its own class
arguments are omitted from the syntax and are generalized using
automatic names, without instance search. Other arguments are also
generalized unless provided. This produces a fully general statement.
this behavior may be disabled by prefixing the type with a ``!`` or
by forcing the typeclass name to be an explicit application using
``@`` (however the later ignores implicit argument information).

.. rocqtop:: all

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

.. rocqtop:: all

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
