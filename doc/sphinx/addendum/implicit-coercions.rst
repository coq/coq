.. _coercions:

Implicit Coercions
====================

:Author: Amokrane Saïbi

General Presentation
---------------------

This section describes one inheritance mechanism of the Rocq Prover. With
inheritance, we are not interested in adding any expressive power to
our theory, but only convenience. Given a term, possibly not typable,
we are interested in the problem of determining if it can be well
typed modulo insertion of appropriate coercions. We allow to write:

 * :g:`f a` where :g:`f:(forall x:A,B)` and :g:`a:A'` when ``A'`` can
   be seen in some sense as a subtype of ``A``.
 * :g:`x:A` when ``A`` is not a type, but can be seen in
   a certain sense as a type: set, group, category etc.
 * :g:`f a` when ``f`` is not a function, but can be seen in a certain sense
   as a function: bijection, functor, any structure morphism etc.

.. _classes-implicit-coercions:

Coercion Classes
----------------

A class with :math:`n` parameters is any defined name with a type
:n:`forall (@ident__1 : @type__1)..(@ident__n:@type__n), @sort`.  Thus a class with
parameters is considered as a single class and not as a family of
classes.  An object of a coercion class is any term of type
:n:`@coercion_class @term__1 .. @term__n`.
In addition to these user-defined classes, we have two built-in classes:


  * ``Sortclass``, the class of sorts; its objects are the terms whose type is a
    sort (e.g. :g:`Prop` or :g:`Type`).
  * ``Funclass``, the class of functions; its objects are all the terms with a functional
    type, i.e. of form :g:`forall x:A,B`.

Formally, the syntax of classes is defined as:

   .. insertprodn coercion_class coercion_class

   .. prodn::
      coercion_class ::= Funclass
      | Sortclass
      | @reference


.. note::
   Don't confuse coercion classes with typeclasses, which are records with
   special properties defined with the :cmd:`Class` command.

Coercions
---------

A name ``f`` can be declared as a coercion between a source user-defined class
``C`` with :math:`n` parameters and a target class ``D`` if one of these
conditions holds:

 * ``D`` is a user-defined class, then the type of ``f`` must have the form
   :g:`forall (x₁:A₁)..(xₖ:Aₖ)(y:C v₁..vₙ), D u₁..uₘ` where :math:`m`
   is the number of parameters of ``D``.
 * ``D`` is ``Funclass``, then the type of ``f`` must have the form
   :g:`forall (x₁:A₁)..(xₖ:Aₖ)(y:C v₁..vₙ)(x:A), B`.
 * ``D`` is ``Sortclass``, then the type of ``f`` must have the form
   :g:`forall (x₁:A₁)..(xₖ:Aₖ)(y:C v₁..vₙ), s` with ``s`` a sort.

We then write :g:`f : C >-> D`.

.. _ambiguous-paths:

When you declare a new coercion (e.g. with :cmd:`Coercion`), new coercion
paths with the same classes as existing ones are ignored. Rocq will generate
a warning when the two paths may be non convertible. When the :g:`x₁..xₖ` are exactly
the :g:`v₁..vₙ` (in the same order), the coercion is said to satisfy
the :gdef:`uniform inheritance condition`. When possible, we recommend
using coercions that satisfy this condition. This guarantees that
no spurious warning will be generated.

.. note:: The built-in class ``Sortclass`` can be used as a source class, but
          the built-in class ``Funclass`` cannot.

To coerce an object :g:`t:C t₁..tₙ` of ``C`` towards ``D``, we have to
apply the coercion ``f`` to it; the obtained term :g:`f _.._ t` is
then an object of ``D``.

Reversible Coercions
--------------------

When a term cannot be coerced (directly) to its expected type, Rocq tries to
use a :gdef:`reversible coercion` (see the :attr:`reversible` attribute). Intuitively,
Rocq synthesizes a new term of the right type that can be coerced
to the original one. The new term is obtained by reversing the coercion, that
is guessing its input given the output.

More precisely, in order to coerce a term :g:`a : A` to type :g:`B`, Rocq
finds a reversible coercion :g:`f : B >-> A`, then synthesizes some :g:`?x : B`
such that :g:`f ?x = a` (typically through :ref:`canonicalstructures` or
:ref:`typeclasses`) and finally replaces :g:`a` with the value of :g:`?x`.

If Rocq doesn't find a reversible coercion :g:`f : B >-> A`, then it
looks for a coercion class :g:`C` equipped with an incoming reversible coercion
:g:`g : B >-> C` and a coercion :g:`h : A >-> C` (not necessarily reversible),
then synthesizes some :g:`?x : B` such that :g:`g ?x = h a`, and finally
replaces :g:`a` with the value of :g:`?x`.
If there's another class :g:`D` with a coercion from :g:`C` to :g:`D` and
incoming coercions from :g:`A` and :g:`B`, Rocq tries :g:`C` before :g:`D`.
This ordering is well defined only if the coercion graph happens to be a semi
lattice.  The intuition behind this ordering is that since coercions forget
information, :g:`D` has less information that :g:`C`, and hence
inferring :g:`?x : B` from :g:`h a : D` would be harder.

See the :ref:`example below <example-reversible-coercion>`.

Identity Coercions
-------------------

To make coercions work for both a named class and for
``Sortclass`` or ``Funclass``, use the :cmd:`Identity Coercion` command.
There is an example :ref:`here <example-identity-coercion>`.

Inheritance Graph
------------------

Coercions form an inheritance graph with classes as nodes.  We call
*coercion path* an ordered list of coercions between two nodes of
the graph.  A class ``C`` is said to be a subclass of ``D`` if there is a
coercion path in the graph from ``C`` to ``D``; we also say that ``C``
inherits from ``D``. Our mechanism supports multiple inheritance since a
class may inherit from several classes, contrary to simple inheritance
where a class inherits from at most one class.  However there must be
at most one path between two classes. If this is not the case, only
the *oldest* one is valid and the others are ignored. So the order
of declaration of coercions is important.

We extend notations for coercions to coercion paths. For instance
:g:`[f₁;..;fₖ] : C >-> D` is the coercion path composed
by the coercions ``f₁..fₖ``.  The application of a coercion path to a
term consists of the successive application of its coercions.


Coercion Classes
----------------

.. cmd:: Coercion @reference {? : @coercion_class >-> @coercion_class }
         Coercion @ident_decl @def_body

  The first form declares the construction denoted by :token:`reference` as a coercion between
  the two given classes.  The second form defines :token:`ident_decl`
  just like :cmd:`Definition` :n:`@ident_decl @def_body`
  and then declares :token:`ident_decl` as a coercion between it source and its target.
  Both forms support the :attr:`local` attribute, which makes the coercion local to the current section.

  :n:`{? : @coercion_class >-> @coercion_class }`
    The source and target classes of the coercion.
    If unspecified, :n:`@reference` must already be a coercion, which
    enables modifying the :attr:`reversible` attribute of :n:`@reference`.
    See the :ref:`example <example-reversible-coercion-attribute>` below.

  .. attr:: reversible{? = {| yes | no } }
     :name: reversible

     This :term:`attribute` allows the coercion to be used as a
     :term:`reversible coercion`. By default coercions are not reversible except for
     :cmd:`Record` fields specified using :g:`:>`.

  .. attr:: nonuniform

     Silence the non uniform inheritance warning.

     .. deprecated:: 8.18

        Use the :attr:`warnings` attribute instead with "-uniform-inheritance".

  .. exn:: @qualid not declared.

     :token:`qualid` is not defined globally.

  .. exn:: @qualid is already a coercion.

     :token:`qualid` is already registered as a coercion.

  .. exn:: Funclass cannot be a source class.

     Funclass as a source class is currently not supported. This may change in
     the future.

  .. exn:: @qualid is not a function.

     :token:`qualid` is not a function, so it cannot be used as a coercion.

  .. exn:: Cannot find the source class of @qualid.

     Rocq can not infer a valid source class.

  .. exn:: Cannot recognize @coercion_class as a source class of @qualid.

     The inferred source class of the coercion differs from the one specified.

  .. exn:: Cannot find the target class

     The target class of the coercion is not specified and cannot be inferred.
     Make sure that the target is not a variable.

  .. exn:: Found target class @coercion_class instead of @coercion_class

     The inferred target class of the coercion differs from the one specified.

  .. warn:: @qualid does not respect the uniform inheritance condition.

     The :ref:`test for ambiguous coercion paths <ambiguous-paths>`
     may yield false positives involving the coercion :token:`qualid`.
     Use the :attr:`warnings` attribute with "-uniform-inheritance" to silence this warning.

  .. warn:: New coercion path ... is ambiguous with existing ...

     The check for :ref:`ambiguous paths <ambiguous-paths>` failed.
     The paths for which this check fails are displayed by a warning
     in the form :g:`[f₁;..;fₙ] : C >-> D`.

     The convertibility checking procedure for coercion paths is complete for
     paths consisting of coercions satisfying the :term:`uniform inheritance condition`,
     but some coercion paths could be reported as ambiguous even if they are
     convertible with existing ones when they have coercions that don't satisfy
     this condition.

  .. warn:: ... is not definitionally an identity function.

     If a coercion path has the same source and target class, that is said to be
     circular. When a new circular coercion path is not convertible with the
     identity function, it will be reported as ambiguous.

Some objects can be declared as coercions when they are defined.
This applies to :ref:`assumptions<gallina-assumptions>` and
constructors of :ref:`inductive types and record fields<gallina-inductive-definitions>`.
Use :n:`:>` instead of :n:`:` before the
type of the assumption to do so.  See :n:`@of_type`.


.. cmd:: Identity Coercion @ident : @coercion_class__src >-> @coercion_class__dest


   Checks that :n:`@coercion_class__src` is a :term:`constant` with a :term:`body` of the form
   :n:`fun (x₁:T₁)..(xₙ:Tₙ) => @coercion_class__dest t₁..tₘ` where `m` is the
   number of parameters of :n:`@coercion_class__dest`.  Then we define an identity
   function with type :g:`forall (x₁:T₁)..(xₙ:Tₙ)(y:C x₁..xₙ),D t₁..tₘ`,
   and we declare it as an identity coercion between ``C`` and ``D``.
   See below for an :ref:`example <example-identity-coercion>`.

   This command supports the :attr:`local` attribute, which makes the coercion local to the current section.

   .. exn:: @coercion_class must be a transparent constant.
      :undocumented:

   .. cmd:: SubClass @ident_decl @def_body

      If :n:`@type` is a coercion class :n:`@ident'` applied to some arguments then
      :n:`@ident` is defined and an identity coercion of name
      :n:`Id_@ident_@ident'` is
      declared. In other words, this is an abbreviation for

      :n:`Definition @ident := @type.`
      :n:`Identity Coercion Id_@ident_@ident' : @ident >-> @ident'`.

      This command supports the :attr:`local` attribute, which makes the coercion local to the current section.


Displaying Available Coercions
-------------------------------

.. cmd:: Print Classes

   Print the list of declared coercion classes in the current context.

.. cmd:: Print Coercions

   Print the list of declared coercions in the current context.

.. cmd:: Print Graph

   Print the list of valid coercion paths in the current context.

.. cmd:: Print Coercion Paths @coercion_class @coercion_class

   Print the list of valid coercion paths between the two given classes.

Activating the Printing of Coercions
-------------------------------------

.. flag:: Printing Coercions

   When on, this :term:`flag` forces all the coercions to be printed.
   By default, coercions are not printed.

.. table:: Printing Coercion @qualid

   This :term:`table` specifies a set of qualids for which coercions are always displayed.  Use the
   :cmd:`Add` and :cmd:`Remove` commands to update the set of qualids.

.. _coercions-classes-as-records:

Classes as Records
------------------

.. index:: :> (coercion)

*Structures with Inheritance* may be defined using the :cmd:`Record` command.

Use `>` before the record name to declare the constructor name as
a coercion from the class of the last field type to the record name.
See :token:`record_definition`.

Use `:>` in the field type to declare the field as a coercion from the
record name to the class of the field type. For these coercions, the
:attr:`reversible` attribute defaults to :g:`yes`. See :token:`of_type`.

Coercions and Sections
----------------------

The inheritance mechanism is compatible with the section
mechanism. The global classes and coercions defined inside a section
are redefined after its closing, using their new value and new
type. The classes and coercions which are local to the section are
simply forgotten.
Coercions with a local source class or a local target class
are also forgotten.

Coercions and Modules
---------------------

The coercions present in a module are activated only when the module is
explicitly imported.

Examples
--------

There are three situations:

.. example:: Coercion at function application

  :g:`f a` is ill-typed where :g:`f:forall x:A,B` and :g:`a:A'`. If there is a
  coercion path between ``A'`` and ``A``, then :g:`f a` is transformed into
  :g:`f a'` where ``a'`` is the result of the application of this
  coercion path to ``a``.

  We first give an example of coercion between atomic inductive types

  .. rocqtop:: all

    Definition bool_in_nat (b:bool) := if b then 0 else 1.
    Coercion bool_in_nat : bool >-> nat.
    Check (0 = true).
    Set Printing Coercions.
    Check (0 = true).
    Unset Printing Coercions.

  .. warning::

    Note that ``Check (true = O)`` would fail. This is "normal" behavior of
    coercions. To validate ``true=O``, the coercion is searched from
    ``nat`` to ``bool``. There is none.

  We give an example of coercion between classes with parameters.

  .. rocqtop:: all

    Parameters (C : nat -> Set) (D : nat -> bool -> Set) (E : bool -> Set).
    Parameter f : forall n:nat, C n -> D (S n) true.
    Coercion f : C >-> D.
    Parameter g : forall (n:nat) (b:bool), D n b -> E b.
    Coercion g : D >-> E.
    Parameter c : C 0.
    Parameter T : E true -> nat.
    Check (T c).
    Set Printing Coercions.
    Check (T c).
    Unset Printing Coercions.

  In the case of functional arguments, we use the monotonic rule of
  sub-typing. To coerce :g:`t : forall x : A, B` towards
  :g:`forall x : A', B'`, we have to coerce ``A'`` towards ``A`` and ``B``
  towards ``B'``. An example is given below:

  .. rocqtop:: all

    Parameters (A B : Set) (h : A -> B).
    Coercion h : A >-> B.
    Parameter U : (A -> E true) -> nat.
    Parameter t : B -> C 0.
    Check (U t).
    Set Printing Coercions.
    Check (U t).
    Unset Printing Coercions.

  Remark the changes in the result following the modification of the
  previous example.

  .. rocqtop:: all

    Parameter U' : (C 0 -> B) -> nat.
    Parameter t' : E true -> A.
    Check (U' t').
    Set Printing Coercions.
    Check (U' t').
    Unset Printing Coercions.

.. example:: Coercion to a type

  An assumption ``x:A`` when ``A`` is not a type, is ill-typed.  It is
  replaced by ``x:A'`` where ``A'`` is the result of the application to
  ``A`` of the coercion path between the class of ``A`` and
  ``Sortclass`` if it exists.  This case occurs in the abstraction
  :g:`fun x:A => t`, universal quantification :g:`forall x:A,B`, global
  variables and parameters of (co)inductive definitions and
  functions. In :g:`forall x:A,B`, such a coercion path may also be applied
  to ``B`` if necessary.

  .. rocqtop:: all

    Parameter Graph : Type.
    Parameter Node : Graph -> Type.
    Coercion Node : Graph >-> Sortclass.
    Parameter G : Graph.
    Parameter Arrows : G -> G -> Type.
    Check Arrows.
    Parameter fg : G -> G.
    Check fg.
    Set Printing Coercions.
    Check fg.
    Unset Printing Coercions.

.. example:: Coercion to a function

  ``f a`` is ill-typed because ``f:A`` is not a function. The term
  ``f`` is replaced by the term obtained by applying to ``f`` the
  coercion path between ``A`` and ``Funclass`` if it exists.

  .. rocqtop:: all

    Parameter bij : Set -> Set -> Set.
    Parameter ap : forall A B:Set, bij A B -> A -> B.
    Coercion ap : bij >-> Funclass.
    Parameter b : bij nat nat.
    Check (b 0).
    Set Printing Coercions.
    Check (b 0).
    Unset Printing Coercions.

.. _example-reversible-coercion:

.. example:: Reversible coercions

  Notice the :n:`:>` on `ssort` making it a :term:`reversible coercion`.

  .. rocqtop:: in

    Structure S := {
      ssort :> Type;
      sstuff : ssort;
    }.
    Definition test (s : S) := sstuff s.
    Canonical Structure S_nat := {| ssort := nat; sstuff := 0; |}.

  .. rocqtop:: all

    Check test (nat : Type).

.. _example-reversible-coercion-attribute:

.. example:: Reversible coercions using the :attr:`reversible` attribute

  Notice there is no `:>` on `ssort'` and the added :cmd:`Coercion` compared
  to the previous example.

  .. rocqtop:: in

    Structure S' := {
      ssort' : Type;
      sstuff' : ssort';
    }.
    Coercion ssort' : S' >-> Sortclass.
    Definition test' (s : S') := sstuff' s.
    Canonical Structure S_nat' := {| ssort' := nat; sstuff' := 0; |}.

  Since there's no `:>` on the definition of `ssort'`, the :attr:`reversible` attribute is not set:

  .. rocqtop:: all

    Fail Check test' (nat : Type).

  The attribute can be set after declaring the coercion:

  .. rocqtop:: all

    #[reversible] Coercion ssort'.
    Check test' (nat : Type).

.. _example-identity-coercion:

.. example:: Identity coercions.

  .. rocqtop:: in

    Definition fct := nat -> nat.
    Parameter incr_fct : Set.
    Parameter fct_of_incr_fct : incr_fct -> fct.

  .. rocqtop:: all

    Fail Coercion fct_of_incr_fct : incr_fct >-> Funclass.

  .. rocqtop:: in

    Coercion fct_of_incr_fct : incr_fct >-> fct.
    Parameter f' : incr_fct.

  .. rocqtop:: all

    Check f' : fct.
    Fail Check f' 0.
    Identity Coercion Id_fct_Funclass : fct >-> Funclass.
    Check f' 0.

.. example:: Inheritance Graph

  Let us see the resulting graph after all these examples.

  .. rocqtop:: all

    Print Graph.
