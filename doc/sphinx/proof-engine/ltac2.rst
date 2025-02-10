.. _ltac2:

Ltac2
=====

.. _ltac2_design:

General design
--------------

There are various alternatives to Ltac1, such as Mtac or Rtac for instance.
While those alternatives can be quite different from Ltac1, we designed
Ltac2 to be as close as reasonably possible to Ltac1, while fixing its
:ref:`defects <ltac_defects>`.

In particular, Ltac2 is:

- a member of the ML family of languages, i.e.

  * a call-by-value functional language
  * with effects
  * together with the Hindley-Milner type system

- a language featuring meta-programming facilities for the manipulation of
  Rocq-side terms
- a language featuring notation facilities to help write palatable scripts

We describe these in more detail in the remainder of this document.

ML component
------------

Overview
~~~~~~~~

Ltac2 is a member of the ML family of languages, in the sense that it is an
effectful call-by-value functional language, with static typing à la
Hindley-Milner (see :cite:`MilnerPrincipalTypeSchemes`). It is commonly accepted
that ML constitutes a sweet spot in PL design, as it is relatively expressive
while not being either too lax (unlike dynamic typing) nor too strict
(unlike, say, dependent types).

The main goal of Ltac2 is to serve as a meta-language for Rocq. As such, it
naturally fits in the ML lineage, just as the historical ML was designed as
the tactic language for the LCF prover. It can also be seen as a general-purpose
language, by simply forgetting about the Rocq-specific features.

Sticking to a standard ML type system can be considered somewhat weak for a
meta-language designed to manipulate Rocq terms. In particular, there is no
way to statically guarantee that a Rocq term resulting from an Ltac2
computation will be well-typed. This is actually a design choice, motivated
by backward compatibility with Ltac1. Instead, well-typedness is deferred to
dynamic checks, allowing many primitive functions to fail whenever they are
provided with an ill-typed term.

The language is naturally effectful as it manipulates the global state of the
proof engine. This allows to think of proof-modifying primitives as effects
in a straightforward way. Semantically, proof manipulation lives in a monad,
which allows to ensure that Ltac2 satisfies the same equations as a generic ML
with unspecified effects would do, e.g. function reduction is substitution
by a value.

Use the following command to import Ltac2:

.. rocqtop:: in

   From Ltac2 Require Import Ltac2.

Type Syntax
~~~~~~~~~~~

At the level of terms, we simply elaborate on Ltac1 syntax, which is quite
close to OCaml. Types follow the simply-typed syntax of OCaml.

.. insertprodn ltac2_type ltac2_typevar

.. prodn::
   ltac2_type ::= @ltac2_type2 -> @ltac2_type
   | @ltac2_type2
   ltac2_type2 ::= @ltac2_type1 * {+* @ltac2_type1 }
   | @ltac2_type1
   ltac2_type1 ::= @ltac2_type0 @qualid
   | @ltac2_type0
   ltac2_type0 ::= ( {+, @ltac2_type } ) {? @qualid }
   | @ltac2_typevar
   | _
   | @qualid
   ltac2_typevar ::= ' @ident

The set of base types can be extended thanks to the usual ML type
declarations such as algebraic datatypes and records.

Built-in types include:

- ``int``, machine integers (size not specified, in practice inherited from OCaml)
- ``string``, mutable strings
- ``'a array``, mutable arrays
- ``exn``, exceptions
- ``constr``, kernel-side terms
- ``pattern``, term patterns
- ``ident``, well-formed identifiers

Type declarations
~~~~~~~~~~~~~~~~~

One can define new types with the following commands.

.. cmd:: Ltac2 Type {? rec } @tac2typ_def {* with @tac2typ_def }

   .. insertprodn tac2typ_def tac2rec_field

   .. prodn::
      tac2typ_def ::= {? @tac2typ_prm } @qualid {? {| := | ::= } @tac2typ_knd }
      tac2typ_prm ::= @ltac2_typevar
      | ( {+, @ltac2_typevar } )
      tac2typ_knd ::= @ltac2_type
      | [ {? {? %| } {+| @tac2alg_constructor } } ]
      | [ .. ]
      | %{ {? {+; @tac2rec_field } {? ; } } %}
      tac2alg_constructor ::= {* #[ {+, @attribute } ] } @ident
      | {* #[ {+, @attribute } ] } @ident ( {*, @ltac2_type } )
      tac2rec_field ::= {? mutable } @ident : @ltac2_type

   :n:`:=`
     Defines a type with an explicit set of constructors

   :n:`::=`
     Extends an existing open variant type, a special kind of variant type whose constructors are not
     statically defined, but can instead be extended dynamically. A typical example
     is the standard `exn` type for exceptions. Pattern matching on open variants must always
     include a catch-all clause. They can be extended with this form, in which case
     :token:`tac2typ_knd` should be in the form :n:`[ {? {? %| } {+| @tac2alg_constructor } } ]`.

   Without :n:`{| := | ::= }`
     Defines an abstract type for use representing data from OCaml.  Not for
     end users.

   :n:`with @tac2typ_def`
     Permits definition of mutually recursive type definitions.

   In :n:`@tac2alg_constructor`, :n:`attribute` supports :attr:`deprecated` (without `use`)
   and :attr:`warn`.

   Each production of :token:`tac2typ_knd` defines one of four possible kinds
   of definitions, respectively: alias, variant, open variant and record types.

   Aliases are names for a given type expression and are transparently
   unfoldable to that expression. They cannot be recursive.

   .. The non-terminal :token:`uident` designates identifiers starting with an uppercase.

   Variants are sum types defined by constructors and eliminated by
   pattern-matching. They can be recursive, but the `rec` flag must be
   explicitly set. Pattern matching must be exhaustive.

   Open variants can be extended with additional constructors using the `::=` form.

   Records are product types with named fields and eliminated by projection.
   Likewise they can be recursive if the `rec` flag is set.

.. attr:: abstract
   :name: abstract

   Types declared with this attribute are made abstract at the end of
   the current module. This makes it possible to enforce invariants.

   .. example::

      .. rocqtop:: in

         Module PositiveInt.
           #[abstract] Ltac2 Type t := int.

           Ltac2 make (x:int) : t := if Int.le 0 x then x else Control.throw (Invalid_argument None).
           Ltac2 get (x:t) : int := x.
         End PositiveInt.

      .. rocqtop:: all

         Ltac2 Eval PositiveInt.get (PositiveInt.make 3).
         Fail Ltac2 Eval PositiveInt.get (PositiveInt.make -1).

.. cmd:: Ltac2 @ external @ident : @ltac2_type := @string__plugin @string__function
   :name: Ltac2 external

   Declares functions defined in OCaml. :n:`@string__plugin` is the
   plugin name defining the function.  :n:`@string__function` is the internal name
   of the function.

   This command supports the :attr:`deprecated` attribute.

APIs
~~~~

Ltac2 provides over 150 API functions that provide various capabilities.  These
are declared with :cmd:`Ltac2 external` in :n:`lib/coq/user-contrib/Ltac2/*.v`.
For example, `Message.print` defined in `Message.v` is used to print messages:

.. rocqtop:: none

   Goal True.

.. rocqtop:: all abort

   Message.print (Message.of_string "fully qualified calls").
   From Ltac2 Require Import Message.
   print (of_string "unqualified calls").

Term Syntax
~~~~~~~~~~~

The syntax of the functional fragment is very close to that of Ltac1, except
that it adds a true pattern-matching feature, as well as a few standard
constructs from ML.

In practice, there is some additional syntactic sugar that allows the
user to bind a variable and match on it at the same time, in the usual ML style.

There is dedicated syntax for list and array literals.

.. insertprodn ltac2_expr ltac2_atom

.. prodn::
   ltac2_expr ::= @ltac2_expr5 ; @ltac2_expr
   | @ltac2_expr5
   ltac2_expr5 ::= fun {+ @tac2pat0 } {? : @ltac2_type } => @ltac2_expr
   | let {? rec } @ltac2_let_clause {* with @ltac2_let_clause } in @ltac2_expr
   | @ltac2_expr3
   ltac2_let_clause ::= {+ @tac2pat0 } {? : @ltac2_type } := @ltac2_expr
   ltac2_expr3 ::= {+, @ltac2_expr2 }
   ltac2_expr2 ::= @ltac2_expr1 :: @ltac2_expr2
   | @ltac2_expr1
   ltac2_expr1 ::= @ltac2_expr0 {+ @ltac2_expr0 }
   | @ltac2_expr0 .( @qualid )
   | @ltac2_expr0 .( @qualid ) := @ltac2_expr5
   | @ltac2_expr0
   tac2rec_fieldexpr ::= @qualid {? := @ltac2_expr1 }
   ltac2_expr0 ::= ( @ltac2_expr )
   | ( @ltac2_expr : @ltac2_type )
   | ()
   | [ %| {*; @ltac2_expr5 } %| ]
   | [ {*; @ltac2_expr5 } ]
   | %{ @ltac2_expr0 with {? {+; @tac2rec_fieldexpr } {? ; } } %}
   | %{ {? {+; @tac2rec_fieldexpr } {? ; } } %}
   | @ltac2_atom
   tac2rec_fieldpats ::= @tac2rec_fieldpat ; {? @tac2rec_fieldpats }
   | @tac2rec_fieldpat ;
   | @tac2rec_fieldpat
   tac2rec_fieldpat ::= @qualid {? := @tac2pat1 }
   ltac2_atom ::= @integer
   | @string
   | @qualid
   | @ @ident
   | & @ident
   | ' @term
   | @ltac2_quotations

The non-terminal :production:`lident` designates identifiers starting with a
lowercase letter.

:n:`'@term` is equivalent to :n:`open_constr:(@term)`.

Use :n:`@ltac2_expr0 .( @qualid )` to access record fields and
:n:`@ltac2_expr0 .( @qualid ) := @ltac2_expr5` to modify
mutable record fields.

Record expressions and patterns support "punning": in
:n:`@tac2rec_fieldexpr` and :n:`@tac2rec_fieldpat`, omitting the
optional part is equivalent to using :n:`:= @ident` where the
identifier is the identifier part of the field name (i.e. the :n:`@qualid`).

A record value can be built from another by changing only a subset of
its fields with the syntax :n:`%{ @ltac2_expr0 with {? {+; @qualid := @ltac2_expr1 } {? ; } } %}`. Fields
that are not explicitly assigned a value take
their value from :n:`@ltac2_expr0`.

Ltac2 Definitions
~~~~~~~~~~~~~~~~~

.. cmd:: Ltac2 {? mutable } {? rec } @tac2def_body {* with @tac2def_body }

   .. insertprodn tac2def_body tac2def_body

   .. prodn::
      tac2def_body ::= {| _ | @ident } {* @tac2pat0 } {? : @ltac2_type } := @ltac2_expr

   This command defines a new global Ltac2 value.  If one or more :token:`tac2pat0`
   are specified, the new value is a function.  This is a shortcut for one of the
   :token:`ltac2_expr5` productions.  For example: :n:`Ltac2 foo a b := …` is equivalent
   to :n:`Ltac2 foo := fun a b => …`.

   The body of an Ltac2 definition is required to be a syntactical value
   that is, a function, a constant, a pure constructor recursively applied to
   values or a (non-recursive) let binding of a value in a value.

   If ``rec`` is set, the tactic is expanded into a recursive binding.

   If ``mutable`` is set, the definition can be redefined at a later stage (see below).

   This command supports the :attr:`deprecated` attribute.

.. cmd:: Ltac2 Set @qualid {? as @ident } := @ltac2_expr

   This command redefines a previous ``mutable`` definition.
   Mutable definitions act like dynamic binding, i.e. at runtime, the last defined
   value for this entry is chosen. This is useful for global flags and the like.
   The previous value of the binding can be optionally accessed using the `as`
   binding syntax.

   The effect of this command is limited to the current section or module.
   When not in a section, importing the module containing this command
   applies the redefinition again.
   In other words it acts according to :attr:`local` in sections and
   :attr:`export` otherwise (but explicit locality is not supported).

   .. example:: Dynamic nature of mutable cells

      .. rocqtop:: all

         Ltac2 mutable x := true.
         Ltac2 y () := x.
         Ltac2 Eval y ().
         Ltac2 Set x := false.
         Ltac2 Eval y ().

   .. example:: Interaction with recursive calls

      .. rocqtop:: all

         Ltac2 mutable rec f b := if b then 0 else f true.
         Ltac2 Set f := fun b => if b then 1 else f true.
         Ltac2 Eval (f false).
         Ltac2 Set f as oldf := fun b => if b then  2 else oldf false.
         Ltac2 Eval (f false).

      In the definition, the `f` in the body is resolved statically
      because the definition is marked recursive. It is equivalent to
      `Ltac2 mutable f x := let rec g b := if b then 0 else g true in g x`
      (alpha renaming the internal `f` to `g` to make the behavior clearer).
      In the first re-definition, the `f` in the body is resolved dynamically.
      This is witnessed by the second re-definition.

Printing Ltac2 tactics
~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Ltac2 @qualid

   :cmd:`Print` can print defined Ltac2 tactics and can avoid printing
   other objects by using `Print Ltac2`.

.. cmd:: Print Ltac2 Type @qualid

   Prints the definitions of ltac2 types.

.. cmd:: Ltac2 Globalize @ltac2_expr

   Prints the result of resolving notations in the given expression.

.. cmd:: Ltac2 Check @ltac2_expr

   Typechecks the given expression and prints the result.

.. cmd:: Print Ltac2 Signatures

   This command displays a list of all defined tactics in scope with their types.

Reduction
~~~~~~~~~

We use the usual ML call-by-value reduction, with an otherwise unspecified
evaluation order. This is a design choice making it compatible with OCaml,
if ever we implement native compilation. The expected equations are as follows::

  (fun x => t) V ≡ t{x := V} (βv)

  let x := V in t ≡ t{x := V} (let)

  match C V₀ ... Vₙ with ... | C x₀ ... xₙ  => t | ... end ≡ t {xᵢ := Vᵢ} (ι)

  (t any term, V values, C constructor)

Note that call-by-value reduction is already a departure from Ltac1 which uses
heuristics to decide when to evaluate an expression. For instance, the following
expressions do not evaluate the same way in Ltac1.

:n:`foo (idtac; let x := 0 in bar)`

:n:`foo (let x := 0 in bar)`

Instead of relying on the :n:`idtac` idiom, we would now require an explicit thunk
to not compute the argument, and :n:`foo` would have e.g. type
:n:`(unit -> unit) -> unit`.

:n:`foo (fun () => let x := 0 in bar)`

Typing
~~~~~~

Typing is strict and follows the Hindley-Milner system. Unlike Ltac1, there
are no type casts at runtime, and one has to resort to conversion
functions. See notations though to make things more palatable.

In this setting, all the usual argument-free tactics have type :n:`unit -> unit`, but
one can return a value of type :n:`t` thanks to terms of type :n:`unit -> t`,
or take additional arguments.

Effects
~~~~~~~

Effects in Ltac2 are straightforward, except that instead of using the
standard IO monad as the ambient effectful world, Ltac2 has a tactic monad.

Note that the order of evaluation of application is *not* specified and is
implementation-dependent, as in OCaml.

We recall that the `Proofview.tactic` monad is essentially a IO monad together
with backtracking state representing the proof state.

Intuitively a thunk of type :n:`unit -> 'a` can do the following:

- It can perform non-backtracking IO like printing and setting mutable variables
- It can fail in a non-recoverable way
- It can use first-class backtracking. One way to think about this is that
  thunks are isomorphic to this type:
  :n:`(unit -> 'a) ~ (unit -> exn + ('a * (exn -> 'a)))`
  i.e. thunks can produce a lazy list of results where each
  tail is waiting for a continuation exception.
- It can access a backtracking proof state, consisting among other things of
  the current evar assignment and the list of goals under focus.

We now describe more thoroughly the various effects in Ltac2.

Standard IO
+++++++++++

The Ltac2 language features non-backtracking IO, notably mutable data and
printing operations.

Mutable fields of records and built-in types like `string` and `array`
feature imperative assignment. See modules `String` and `Array`
respectively.

A few printing primitives are provided in the `Message` module for
displaying information to the user.

Fatal errors
++++++++++++

The Ltac2 language provides non-backtracking exceptions, also known as *panics*,
through the following primitive in module `Control`::

  val throw : exn -> 'a

Unlike backtracking exceptions from the next section, this kind of error
is never caught by backtracking primitives, that is, throwing an exception
destroys the stack. This is codified by the following equation, where `E`
is an evaluation context::

  E[throw e] ≡ throw e

  (e value)

There is currently no way to catch such an exception, which is a deliberate design choice.
Eventually there might be a way to catch it and
destroy all backtrack and return values.

Backtracking
++++++++++++

In Ltac2, we have the following backtracking primitives, defined in the
`Control` module::

  Ltac2 Type 'a result := [ Val ('a) | Err (exn) ].

  val zero : exn -> 'a
  val plus : (unit -> 'a) -> (exn -> 'a) -> 'a
  val case : (unit -> 'a) -> ('a * (exn -> 'a)) result

If one views thunks as lazy lists, then `zero` is the empty list and `plus` is
list concatenation, while `case` is pattern-matching.

The backtracking is first-class, i.e. one can write
:n:`plus (fun () => "x") (fun _ => "y") : string` producing a backtracking string.

These operations are expected to satisfy a few equations, most notably that they
form a monoid compatible with sequentialization.::

  plus t zero ≡ t ()
  plus (fun () => zero e) f ≡ f e
  plus (plus t f) g ≡ plus t (fun e => plus (f e) g)

  case (fun () => zero e) ≡ Err e
  case (fun () => plus (fun () => t) f) ≡ Val (t,f)

  let x := zero e in u ≡ zero e
  let x := plus t f in u ≡ plus (fun () => let x := t in u) (fun e => let x := f e in u)

  (t, u, f, g, e values)

Goals
+++++

A goal is given by the data of its conclusion and hypotheses, i.e. it can be
represented as `[Γ ⊢ A]`.

The tactic monad naturally operates over the whole proofview, which may
represent several goals, including none. Thus, there is no such thing as
*the current goal*. Goals are naturally ordered, though.

It is natural to do the same in Ltac2, but we must provide a way to get access
to a given goal. This is the role of the `enter` primitive, which applies a
tactic to each currently focused goal in turn::

  val enter : (unit -> unit) -> unit

It is guaranteed that when evaluating `enter f`, `f` is called with exactly one
goal under focus. Note that `f` may be called several times, or never, depending
on the number of goals under focus before the call to `enter`.

Accessing the goal data is then implicit in the Ltac2 primitives, and may panic
if the invariants are not respected. The two essential functions for observing
goals are given below.::

  val hyp : ident -> constr
  val goal : unit -> constr

The two above functions panic if there is not exactly one goal under focus.
In addition, `hyp` may also fail if there is no hypothesis with the
corresponding name.

Meta-programming
----------------

Overview
~~~~~~~~

One of the major implementation issues of Ltac1 is the fact that it is
never clear whether an object refers to the object world or the meta-world.
This is an incredible source of slowness, as the interpretation must be
aware of bound variables and must use heuristics to decide whether a variable
is a proper one or referring to something in the Ltac context.

Likewise, in Ltac1, constr parsing is implicit, so that ``foo 0`` is
not ``foo`` applied to the Ltac integer expression ``0`` (|Ltac| does have a
notion of integers, though it is not first-class), but rather the Rocq term
:g:`Datatypes.O`.

The implicit parsing is confusing to users and often gives unexpected results.
Ltac2 makes these explicit using quoting and unquoting notation, although there
are notations to do it in a short and elegant way so as not to be too cumbersome
to the user.

Quotations
~~~~~~~~~~

.. _ltac2_built-in-quotations:

Built-in quotations
+++++++++++++++++++

.. insertprodn ltac2_quotations ltac1_expr_in_env

.. prodn::
   ltac2_quotations ::= ident : ( @ident )
   | constr : ( @term )
   | open_constr : ( @term )
   | preterm : ( @term )
   | pat : ( @cpattern )
   | reference : ( {| & @ident | @qualid } )
   | ltac1 : ( @ltac1_expr_in_env )
   | ltac1val : ( @ltac1_expr_in_env )
   ltac1_expr_in_env ::= @ltac_expr
   | {* @ident } %|- @ltac_expr

The current implementation recognizes the following built-in quotations:

- ``ident``, which parses identifiers (type ``Init.ident``).
- ``constr``, which parses Rocq terms and produces an-evar free term at runtime
  (type ``Init.constr``).
- ``open_constr``, which parses Rocq terms and produces a term potentially with
  holes at runtime (type ``Init.constr`` as well).
- ``preterm``, which parses Rocq terms and produces a value which must
  be typechecked with ``Constr.pretype`` (type ``Init.preterm``).
- ``pat``, which parses Rocq patterns and produces a pattern used for term
  matching (type ``Init.pattern``).
- ``reference``  Qualified names
  are globalized at internalization into the corresponding global reference,
  while ``&id`` is turned into ``Std.VarRef id``. This produces at runtime a
  ``Std.reference``.
- ``ltac1``, for calling Ltac1 code, described in :ref:`simple_api`.
- ``ltac1val``, for manipulating Ltac1 values, described in :ref:`low_level_api`.

The following syntactic sugar is provided for two common cases:

- ``@id`` is the same as ``ident:(id)``
- :n:`'@term` is the same as :n:`open_constr:(@term)`

Strict vs. non-strict mode
++++++++++++++++++++++++++

Depending on the context, quotation-producing terms (i.e. ``constr``,
``open_constr`` or ``preterm``) are not internalized in the same way.
There are two possible modes, the *strict* and the *non-strict* mode.

- In strict mode, all simple identifiers appearing in a term quotation are
  required to be resolvable statically. That is, they must be the short name of
  a declaration which is defined globally, excluding section variables and
  hypotheses. If this doesn't hold, internalization will fail. To work around
  this error, one has to specifically use the ``&`` notation.
- In non-strict mode, any simple identifier appearing in a term quotation which
  is not bound in the global environment is turned into a dynamic reference to a
  hypothesis. That is to say, internalization will succeed, but the evaluation
  of the term at runtime will fail if there is no such variable in the dynamic
  context.

Strict mode is enforced by default, such as for all Ltac2 definitions. Non-strict
mode is only set when evaluating Ltac2 snippets in interactive proof mode. The
rationale is that it is cumbersome to explicitly add ``&`` interactively, while it
is expected that global tactics enforce more invariants on their code.

.. _term-antiquotations:

Term Antiquotations
~~~~~~~~~~~~~~~~~~~

Syntax
++++++

One can also insert Ltac2 code into Rocq terms, similar to what is possible in
Ltac1.

.. prodn::
   term += ltac2:( @ltac2_expr )

Antiquoted terms are expected to have type ``unit``, as they are only evaluated
for their side-effects.

Semantics
+++++++++

A quoted Rocq term is interpreted in two phases, internalization and
evaluation.

- Internalization is part of the static semantics, that is, it is done at Ltac2
  typing time.
- Evaluation is part of the dynamic semantics, that is, it is done when
  a term gets effectively computed by Ltac2.

Note that typing of Rocq terms is a *dynamic* process occurring at Ltac2
evaluation time, and not at Ltac2 typing time.

Static semantics
****************

During internalization, Rocq variables are resolved and antiquotations are
type checked as Ltac2 terms, effectively producing a ``glob_constr`` in Rocq
implementation terminology. Note that although it went through the
type checking of **Ltac2**, the resulting term has not been fully computed and
is potentially ill-typed as a runtime **Rocq** term.

.. example::

   The following term is valid (with type `unit -> constr`), but will fail at runtime:

   .. rocqtop:: in

      Ltac2 myconstr () := constr:(nat -> 0).

Term antiquotations are type checked in the enclosing Ltac2 typing context
of the corresponding term expression.

.. example::

   The following will type check, with type `constr`.

   .. rocqdoc::

      let x := '0 in constr:(1 + ltac2:(exact $x))

Beware that the typing environment of antiquotations is **not**
expanded by the Rocq binders from the term.

  .. example::

     The following Ltac2 expression will **not** type check::

     `constr:(fun x : nat => ltac2:(exact $x))`
     `(* Error: Unbound variable 'x' *)`

There is a simple reason for that, which is that the following expression would
not make sense in general.

`constr:(fun x : nat => ltac2:(clear @x; exact x))`

Indeed, a hypothesis can suddenly disappear from the runtime context if some
other tactic pulls the rug from under you.

Rather, the tactic writer has to resort to the **dynamic** goal environment,
and must write instead explicitly that she is accessing a hypothesis, typically
as follows.

`constr:(fun x : nat => ltac2:(exact (hyp @x)))`

This pattern is so common that we provide dedicated Ltac2 and Rocq term notations
for it.

- `&x` as an Ltac2 expression expands to `hyp @x`.
- `&x` as a Rocq constr expression expands to
  `ltac2:(Control.refine (fun () => hyp @x))`.

In the special case where Ltac2 antiquotations appear inside a Rocq term
notation, the notation variables are systematically bound in the body
of the tactic expression with type `Ltac2.Init.preterm`. Such a type represents
untyped syntactic Rocq expressions, which can by typed in the
current context using the `Ltac2.Constr.pretype` function.

.. example::

   The following notation is essentially the identity.

   .. rocqtop:: in

      Notation "[ x ]" := ltac2:(let x := Ltac2.Constr.pretype x in exact $x) (only parsing).

Dynamic semantics
*****************

During evaluation, a quoted term is fully evaluated to a kernel term, and is
in particular type checked in the current environment.

Evaluation of a quoted term goes as follows.

- The quoted term is first evaluated by the pretyper.
- Antiquotations are then evaluated in a context where there is exactly one goal
  under focus, with the hypotheses coming from the current environment extended
  with the bound variables of the term, and the resulting term is fed into the
  quoted term.

Relative orders of evaluation of antiquotations and quoted term are not
specified.

For instance, in the following example, `tac` will be evaluated in a context
with exactly one goal under focus, whose last hypothesis is `H : nat`. The
whole expression will thus evaluate to the term :g:`fun H : nat => H`.

`let tac () := hyp @H in constr:(fun H : nat => ltac2:(tac ()))`

Many standard tactics perform type checking of their argument before going
further. It is your duty to ensure that terms are well-typed when calling
such tactics. Failure to do so will result in non-recoverable exceptions.

**Trivial Term Antiquotations**

It is possible to refer to a variable of type `constr` in the Ltac2 environment
through a specific syntax consistent with the antiquotations presented in
the notation section.

.. prodn:: term += $@lident

or equivalently

.. prodn:: term += $constr:@lident

In a Rocq term, writing :g:`$x` is semantically equivalent to
:g:`ltac2:(Control.refine (fun () => x))`, up to re-typechecking. It allows to
insert in a concise way an Ltac2 variable of type :n:`constr` into a Rocq term.

Similarly variables of type `preterm` have an antiquotation

.. prodn:: term += $preterm:@lident

It is equivalent to pretyping the preterm with the appropriate typing constraint.

Variables of type `pattern` have an antiquotation

.. prodn:: term += $pattern:@lident

Its use is only allowed when producing a pattern, i.e.
`pattern:($pattern:x -> True)` is allowed but
`constr:($pattern:x -> True)` is not allowed. Conversely `constr` and `preterm`
antiquotations are not allowed when producing a pattern.

Match over terms
~~~~~~~~~~~~~~~~

Ltac2 features a construction similar to Ltac1 :tacn:`match` over terms, although
in a less hard-wired way.

.. tacn:: @ltac2_match_key @ltac2_expr__term with @ltac2_match_list end
   :name: lazy_match!; match!; multi_match!

   .. insertprodn ltac2_match_key ltac2_match_pattern

   .. prodn::
      ltac2_match_key ::= lazy_match!
      | match!
      | multi_match!
      ltac2_match_list ::= {? %| } {+| @ltac2_match_rule }
      ltac2_match_rule ::= @ltac2_match_pattern => @ltac2_expr
      ltac2_match_pattern ::= @cpattern
      | context {? @ident } [ @cpattern ]

   Evaluates :n:`@ltac2_expr__term`, which must yield a term, and matches it
   sequentially with the :token:`ltac2_match_pattern`\s, which may contain
   metavariables.  When a match is found, metavariable values are substituted
   into :n:`@ltac2_expr`, which is then applied.

   Matching may continue depending on whether  `lazy_match!`, `match!` or `multi_match!`
   is specified.

   In the :token:`ltac2_match_pattern`\s, metavariables have the form :n:`?@ident`, whereas
   in the :n:`@ltac2_expr`\s, the question mark is omitted.

   .. todo how does this differ from the 1-2 other unification routines elsewhere in Rocq?

   Matching is non-linear: if a
   metavariable occurs more than once, each occurrence must match the same
   expression.  Expressions match if they are syntactically equal or are
   :term:`α-convertible <alpha-convertible>`.
   Matching is first-order except on variables of the form :n:`@?@ident`
   that occur in the head position of an application. For these variables,
   matching is second-order and returns a functional term.

   .. todo the `@?ident` form is in dangling_pattern_extension_rule, not included in the doc yet
      maybe belongs with "Applications"

   `lazy_match!`
      Causes the match to commit to the first matching branch
      rather than trying a new match if :n:`@ltac2_expr` fails.
      :ref:`Example<ltac2_match_vs_lazymatch_ex>`.

   `match!`
      If :n:`@ltac2_expr` fails, continue matching with the next branch.
      Failures in subsequent tactics (after the `match!`) will not cause selection
      of a new branch.  Examples :ref:`here<ltac2_match_vs_lazymatch_ex>` and
      :ref:`here<ltac2_match_vs_multimatch_ex>`.

   `multi_match!`
      If :n:`@ltac2_expr` fails, continue matching with the next branch.
      When a :n:`@ltac2_expr` succeeds for a branch, subsequent failures
      (after the `multi_match!`) causing consumption of all the successes
      of :n:`@ltac2_expr` trigger selection of a new matching branch.
      :ref:`Example<ltac2_match_vs_multimatch_ex>`.

   :n:`@cpattern`
      The syntax of :token:`cpattern` is
      the same as that of :token:`term`\s, but it can contain pattern matching
      metavariables in the form :n:`?@ident` and :n:`@?@ident`.  :g:`_` can be used to match
      irrelevant terms.

      .. todo more on @?@ident here: https://github.com/coq/coq/pull/12085#discussion_r467504046
      .. todo Example is broken :ref:`Example<ltac2_match_with_holes_ex>`.

      .. todo Didn't understand the following 2 paragraphs well enough to revise
         see https://github.com/coq/coq/pull/12103#discussion_r436297754 for a
         possible example

      Unlike Ltac1, Ltac2 :n:`?id` metavariables only match closed terms.

      There is also a special notation for second-order pattern matching: in an
      applicative pattern of the form :n:`@?@ident @ident__1 … @ident__n`,
      the variable :token:`ident` matches any complex expression with (possible)
      dependencies in the variables :n:`@ident__i` and returns a functional term
      of the form :n:`fun @ident__1 … @ident__n => @term`.

   :n:`context {? @ident } [ @cpattern ]`
      Matches any term with a subterm matching :token:`cpattern`. If there is a match
      and :n:`@ident` is present, it is assigned the "matched
      context", i.e. the initial term where the matched subterm is replaced by a
      hole.  This hole in the matched context can be filled with the expression
      :n:`Pattern.instantiate @ident @cpattern`.

      For :tacn:`match!` and :tacn:`multi_match!`, if the evaluation of the :token:`ltac2_expr`
      fails, the next matching subterm is tried. If no further subterm matches, the next branch
      is tried.  Matching subterms are considered from top to bottom and from left to
      right (with respect to the raw printing obtained by setting the
      :flag:`Printing All` flag).  :ref:`Example<ltac2_match_term_context_ex>`.

   .. todo There's a more realistic example from @JasonGross here:
      https://github.com/coq/coq/pull/12103#discussion_r432996954

   :n:`@ltac2_expr`
      The tactic to apply if the construct matches.  Metavariable values from the pattern
      match are statically bound as Ltac2 variables in :n:`@ltac2_expr` before
      it is applied.

      If :n:`@ltac2_expr` is a tactic with backtracking points, then subsequent
      failures after a :tacn:`lazy_match!` or :tacn:`multi_match!` (but not :tacn:`match!`) can cause
      backtracking into :n:`@ltac2_expr` to select its next success.

   Variables from the :n:`@tac2pat1` are statically bound in the body of the branch.
   Variables from the :n:`@term` pattern have values of type `constr`.
   Variables from the :n:`@ident` in the `context` construct have values of type
   `Pattern.context` (defined in `Pattern.v`).

Note that unlike Ltac1, only lowercase identifiers are valid as Ltac2
bindings.  Ltac2 will report an error if one of the bound variables
starts with an uppercase character.

The semantics of this construction are otherwise the same as the corresponding
one from Ltac1, except that it requires the goal to be focused.

.. _ltac2_match_vs_lazymatch_ex:

.. example:: Ltac2 Comparison of lazy_match! and match!

   (Equivalent to this :ref:`Ltac1 example<match_vs_lazymatch_ex>`.)

   These lines define a `msg` tactic that's used in several examples as a more-succinct
   alternative to `print (to_string "...")`:

   .. rocqtop:: in

      From Ltac2 Require Import Message.
      Ltac2 msg x := print (of_string x).

   .. rocqtop:: none

      Goal True.

   In :tacn:`lazy_match!`, if :token:`ltac2_expr` fails, the :tacn:`lazy_match!` fails;
   it doesn't look for further matches.  In :tacn:`match!`, if :token:`ltac2_expr` fails
   in a matching branch, it will try to match on subsequent branches.  Note that
   :n:`'@term` below is equivalent to :n:`open_constr:(@term)`.

   .. rocqtop:: all

      Fail lazy_match! 'True with
      | True => msg "branch 1"; fail
      | _ => msg "branch 2"
      end.

      match! 'True with
      | True => msg "branch 1"; fail
      | _ => msg "branch 2"
      end.

.. _ltac2_match_vs_multimatch_ex:

.. example:: Ltac2 Comparison of match! and multi_match!

   (Equivalent to this :ref:`Ltac1 example<match_vs_multimatch_ex>`.)

   :tacn:`match!` tactics are only evaluated once, whereas :tacn:`multi_match!`
   tactics may be evaluated more than once if the following constructs trigger backtracking:

   .. rocqtop:: all

      Fail match! 'True with
      | True => msg "branch 1"
      | _ => msg "branch 2"
      end ;
      msg "branch A"; fail.

   .. rocqtop:: all

      Fail multi_match! 'True with
      | True => msg "branch 1"
      | _ => msg "branch 2"
      end ;
      msg "branch A"; fail.

.. _ltac2_match_with_holes_ex:

.. todo EXAMPLE DOESN'T WORK: Ltac2 does not (yet?) handle pattern variables matching open terms.
   Matching a pattern with holes

   (Equivalent to this :ref:`Ltac1 example<match_with_holes_ex>`.)

   Notice the :tacn:`idtac` prints ``(z + 1)`` while the :tacn:`pose` substitutes
   ``(x + 1)``.

   .. rocqtop:: all

      match! constr:(fun x => (x + 1) * 3) with
      | fun z => ?y * 3 => print (of_constr y); pose (fun z: nat => $y * 5)
      end.

.. _ltac2_match_term_context_ex:

.. example:: Ltac2 Multiple matches for a "context" pattern.

   (Equivalent to this :ref:`Ltac1 example<match_term_context_ex>`.)

   Internally "x <> y" is represented as "(~ (x = y))", which produces the
   first match.

   .. rocqtop:: in

      Ltac2 f2 t := match! t with
                    | context [ (~ ?t) ] => print (of_constr t); fail
                    | _ => ()
                    end.

   .. rocqtop:: all abort

      f2 constr:((~ True) <> (~ False)).

Match over goals
~~~~~~~~~~~~~~~~

.. tacn:: @ltac2_match_key {? reverse } goal with @goal_match_list end
   :name: lazy_match! goal; match! goal; multi_match! goal

   .. insertprodn goal_match_list gmatch_hyp_pattern

   .. prodn::
      goal_match_list ::= {? %| } {+| @gmatch_rule }
      gmatch_rule ::= @gmatch_pattern => @ltac2_expr
      gmatch_pattern ::= [ {*, @gmatch_hyp_pattern } %|- @ltac2_match_pattern ]
      gmatch_hyp_pattern ::= @name : @ltac2_match_pattern
      | @name := [ @ltac2_match_pattern ] : @ltac2_match_pattern
      | @name := @ltac2_match_pattern

   Matches over goals, similar to Ltac1 :tacn:`match goal`.
   Use this form to match hypotheses and/or goals in the local context.  These patterns have zero or
   more subpatterns to match hypotheses followed by a subpattern to match the conclusion.  Except for the
   differences noted below, this works the same as the corresponding :n:`@ltac2_match_key @ltac2_expr` construct
   (see :tacn:`match!`).  Each current goal is processed independently.

   Matching is non-linear: if a
   metavariable occurs more than once, each occurrence must match the same
   expression.  Within a single term, expressions match if they are syntactically equal or
   :term:`α-convertible <alpha-convertible>`.  When a metavariable is used across
   multiple hypotheses or across a hypothesis and the current goal, the expressions match if
   they are :term:`convertible`.

   .. more detail here: https://github.com/coq/coq/pull/12085#discussion_r470406466

   :n:`{*, @gmatch_pattern }`
      Patterns to match with hypotheses.  Each pattern must match a distinct hypothesis in order
      for the branch to match.

      Hypotheses have the form :n:`@name {? := @term__binder } : @type`.  If :n:`@term__binder` is not specified, the pattern matches hypotheses even if they have a body.

      .. currently only supports the first row
         :list-table::
         :widths: 2 1
         :header-rows: 1

         * - Pattern syntax
           - Example pattern

         * - :n:`@name : @ltac2_match_pattern`
           - `n : ?t`

         * - :n:`@name := @match_pattern__binder`
           - `n := ?b`

         * - :n:`@name := @term__binder : @type`
           - `n := ?b : ?t`

         * - :n:`@name := [ @match_pattern__binder ] : @ltac2_match_pattern`
           - `n := [ ?b ] : ?t`

         :token:`name` can't have a `?`.  Note that the last two forms are equivalent except that:

         - if the `:` in the third form has been bound to something else in a notation, you must use the fourth form.
           Note that cmd:`Require Import` `ssreflect` loads a notation that does this.
         - a :n:`@term__binder` such as `[ ?l ]` (e.g., denoting a singleton list after
           :cmd:`Import` `ListNotations`) must be parenthesized or, for the fourth form,
           use double brackets: `[ [ ?l ] ]`.

      If there are multiple :token:`gmatch_hyp_pattern`\s in a branch, there may be multiple ways to match them to hypotheses.
      For :tacn:`match! goal` and :tacn:`multi_match! goal`, if the evaluation of the :token:`ltac2_expr` fails,
      matching will continue with the next hypothesis combination.  When those are exhausted,
      the next alternative from any `context` construct in the :token:`ltac2_match_pattern`\s is tried and then,
      when the context alternatives are exhausted, the next branch is tried.
      :ref:`Example<ltac2_match_goal_multiple_hyps_ex>`.

   `reverse`
      Hypothesis matching for :token:`gmatch_hyp_pattern`\s normally begins by matching them from left to right,
      to hypotheses, last to first.  Specifying `reverse` begins matching in the reverse order, from
      first to last.  :ref:`Normal<ltac2_match_goal_hyps_ex>` and :ref:`reverse<ltac2_match_goal_hyps_rev_ex>` examples.

   :n:`|- @ltac2_match_pattern`
      A pattern to match with the current goal

   Note that unlike Ltac1, only lowercase identifiers are valid as Ltac2
   bindings.  Ltac2 will report an error if you try to use a bound variable
   that starts with an uppercase character.

   Variables from :n:`@gmatch_hyp_pattern` and :n:`@ltac2_match_pattern` are
   bound in the body of the branch. Their types are:

   - ``constr`` for pattern variables appearing in a :n:`@term`
   - ``Pattern.context`` for variables binding a context
   - ``ident`` for variables binding a hypothesis name.

   The same identifier caveat as in the case of matching over constr applies, and
   this feature has the same semantics as in Ltac1.

.. _ltac2_match_goal_hyps_ex:

.. example:: Ltac2 Matching hypotheses

   (Equivalent to this :ref:`Ltac1 example<match_goal_hyps_ex>`.)

   Hypotheses are matched from the last hypothesis (which is by default the newest
   hypothesis) to the first until the :tacn:`apply` succeeds.

   .. rocqtop:: all abort

      Goal forall A B : Prop, A -> B -> (A->B).
      intros.
      match! goal with
      | [ h : _ |- _ ] => let h := Control.hyp h in print (of_constr h); apply $h
      end.

.. _ltac2_match_goal_hyps_rev_ex:

.. example:: Matching hypotheses with reverse

   (Equivalent to this :ref:`Ltac1 example<match_goal_hyps_rev_ex>`.)

   Hypotheses are matched from the first hypothesis to the last until the :tacn:`apply` succeeds.

   .. rocqtop:: all abort

      Goal forall A B : Prop, A -> B -> (A->B).
      intros.
      match! reverse goal with
      | [ h : _ |- _ ] => let h := Control.hyp h in print (of_constr h); apply $h
      end.

.. _ltac2_match_goal_multiple_hyps_ex:

.. example:: Multiple ways to match a hypotheses

   (Equivalent to this :ref:`Ltac1 example<match_goal_multiple_hyps_ex>`.)

   Every possible match for the hypotheses is evaluated until the right-hand
   side succeeds.  Note that `h1` and `h2` are never matched to the same hypothesis.
   Observe that the number of permutations can grow as the factorial
   of the number of hypotheses and hypothesis patterns.

   .. rocqtop:: all abort

      Goal forall A B : Prop, A -> B -> (A->B).
      intros A B H.
      match! goal with
      | [ h1 : _, h2 : _ |- _ ] =>
         print (concat (of_string "match ")
               (concat (of_constr (Control.hyp h1))
               (concat (of_string " ")
               (of_constr (Control.hyp h2)))));
         fail
      | [ |- _ ] => ()
      end.


.. _ltac2_match_on_values:

Match on values
~~~~~~~~~~~~~~~

.. tacn:: match @ltac2_expr5 with {? @ltac2_branches } end
   :name: match (Ltac2)

   Matches a value, akin to the OCaml `match` construct.  By itself, it doesn't cause backtracking
   as do the `*match*!` and `*match*! goal` constructs.

   .. insertprodn ltac2_branches atomic_tac2pat

   .. prodn::
      ltac2_branches ::= {? %| } {+| {? @atomic_tac2pat } => @ltac2_expr }
      tac2pat1 ::= @qualid {+ @tac2pat0 }
      | @qualid
      | @tac2pat0 :: @tac2pat0
      | @tac2pat0 %| {+| @tac2pat1 }
      | @tac2pat0 as @ident
      | @tac2pat0
      tac2pat0 ::= _
      | ()
      | @integer
      | @string
      | @qualid
      | ( {? @atomic_tac2pat } )
      | %{ {? @tac2rec_fieldpats } %}
      | [ {*; @tac2pat1 } ]
      atomic_tac2pat ::= @tac2pat1 : @ltac2_type
      | @tac2pat1 , {*, @tac2pat1 }
      | @tac2pat1

.. tacn:: if @ltac2_expr5__test then @ltac2_expr5__then else @ltac2_expr5__else
   :name: if-then-else (Ltac2)

   Equivalent to a :tacn:`match <match (Ltac2)>` on a boolean value.  If the
   :n:`@ltac2_expr5__test` evaluates to true, :n:`@ltac2_expr5__then`
   is evaluated.  Otherwise :n:`@ltac2_expr5__else` is evaluated.


.. _ltac2_notations:

Notations
---------

.. cmd:: Ltac2 Notation {+ @ltac2_scope } {? : @natural } := @ltac2_expr

   .. todo seems like name maybe should use lident rather than ident, considering:

      Ltac2 Notation "ex1" X(constr) := print (of_constr X).
      ex1 1.

      Unbound constructor X

      This works fine with lower-case "x" in place of "X"

   .. todo Ltac2 Notation := permits redefining same symbol (no warning)
      Also allows defining a symbol beginning with uppercase, which is prohibited
      in similar constructs.

   :cmd:`Ltac2 Notation` provides a way to extend the syntax of Ltac2 tactics.  The left-hand
   side (before the `:=`) defines the syntax to recognize and gives formal parameter
   names for the syntactic values.  :n:`@integer` is the level of the notation.
   When the notation is used, the values are substituted
   into the right-hand side.  In the following example, `x` is the formal parameter name and
   `constr` is its :ref:`syntactic class<syntactic_classes>`.  `print` and `of_constr` are
   functions provided by Rocq through `Message.v`.
   (Also see :cmd:`Ltac2 Notation (abbreviation)`.)

   .. flag:: Ltac2 Typed Notations

      By default Ltac2 notations are typechecked at declaration time.
      This assigns an expected type to notation arguments.

      When a notation is declared with this flag unset, it is not
      typechecked at declaration time and its expansion is typechecked
      when it is used. This may allow slightly more flexible use of
      the notation arguments at the cost of worse error messages when
      incorrectly using the notation. It is not believed to be useful
      in practice, please report any real use cases you find.

   .. todo "print" doesn't seem to pay attention to "Set Printing All"

   .. example:: Printing a :n:`@term`

      .. rocqtop:: none

         Goal True.

      .. rocqtop:: all

         From Ltac2 Require Import Message.
         Ltac2 Notation "ex1" x(constr) := print (of_constr x).
         ex1 (1 + 2).

      You can also print terms with a regular Ltac2 definition, but then the :n:`@term` must be in
      the quotation `constr:( … )`:

      .. rocqtop:: all

         Ltac2 ex2 x := print (of_constr x).
         ex2 constr:(1+2).

   There are also metasyntactic classes described :ref:`here<syntactic_classes>`
   that combine other items.  For example, `list1(constr, ",")`
   recognizes a comma-separated list of one or more :token:`term`\s.

   .. example:: Parsing a list of :n:`@term`\s

      .. rocqtop:: abort all

         Ltac2 rec print_list x := match x with
         | a :: t => print (of_constr a); print_list t
         | [] => ()
         end.
         Ltac2 Notation "ex2" x(list1(constr, ",")) := print_list x.
         ex2 1, 2, 3.

   An Ltac2 notation adds a parsing rule to the Ltac2 grammar, which is expanded
   to the provided body where every token from the notation is let-bound to the
   corresponding generated expression.

   .. example::

      Assume we perform:

      .. rocqdoc::

         Ltac2 Notation "foo" c(thunk(constr)) ids(list0(ident)) := Bar.f c ids.

      Then the following expression

      `let y := @X in foo (nat -> nat) x $y`

      will expand at parsing time to

      `let y := @X in`
      `let c := fun () => constr:(nat -> nat) with ids := [@x; y] in Bar.f c ids`

      Beware that the order of evaluation of multiple let-bindings is not specified,
      so that you may have to resort to thunking to ensure that side-effects are
      performed at the right time.

   This command supports the :attr:`deprecated` attribute.

   .. exn:: Notation levels must range between 0 and 6.

      The level of a notation must be an integer between 0 and 6 inclusive.

Abbreviations
~~~~~~~~~~~~~

.. cmd:: Ltac2 Notation @ident := @ltac2_expr
   :name: Ltac2 Notation (abbreviation)

   Introduces a special kind of notation, called an abbreviation,
   that does not add any parsing rules. It is similar in
   spirit to Rocq abbreviations (see :cmd:`Notation (abbreviation)`,
   insofar as its main purpose is to give an
   absolute name to a piece of pure syntax, which can be transparently referred to
   by this name as if it were a proper definition.
   (See :cmd:`Ltac2 Notation` for the general description of notations.)

   The abbreviation can then be manipulated just like a normal Ltac2 definition,
   except that it is expanded at internalization time into the given expression.
   Furthermore, in order to make this kind of construction useful in practice in
   an effectful language such as Ltac2, any syntactic argument to an abbreviation
   is thunked on-the-fly during its expansion.

   For instance, suppose that we define the following.

   :n:`Ltac2 Notation foo := fun x => x ().`

   Then we have the following expansion at internalization time.

   :n:`foo 0 ↦ (fun x => x ()) (fun _ => 0)`

   Note that abbreviations are not type checked at all, and may result in typing
   errors after expansion.

   This command supports the :attr:`deprecated` attribute.

.. _defining_tactics:

Defining tactics
~~~~~~~~~~~~~~~~

Built-in tactics (those defined in OCaml code in the Rocq executable) and Ltac1 tactics,
which are defined in `.v` files, must be defined through notations.  (Ltac2 tactics can be
defined with :cmd:`Ltac2`.

Notations for many but not all built-in tactics are defined in `Notations.v`, which is automatically
loaded with Ltac2.  The Ltac2 syntax for these tactics is often identical or very similar to the
tactic syntax described in other chapters of this documentation.  These notations rely on tactic functions
declared in `Std.v`.  Functions corresponding to some built-in tactics may not yet be defined in the
Rocq executable or declared in `Std.v`.  Adding them may require code changes to Rocq or defining
workarounds through Ltac1 (described below).

Two examples of syntax differences:

- There is no notation defined that's equivalent to :n:`intros until {| @ident | @natural }`.  There is,
  however, already an ``intros_until`` tactic function defined ``Std.v``, so it may be possible for a user
  to add the necessary notation.
- The built-in `simpl` tactic in Ltac1 supports the use of scope keys in delta flags, e.g. :n:`simpl ["+"%nat]`
  which is not accepted by Ltac2.  This is because Ltac2 uses a different
  definition for :token:`delta_reductions`; compare it to :token:`ltac2_delta_reductions`.  This also affects
  :tacn:`compute`.

Ltac1 tactics are not automatically available in Ltac2.  (Note that some of the tactics described
in the documentation are defined with Ltac1.)
You can make them accessible in Ltac2 with commands similar to the following
(the example requires the Stdlib library for the :tacn:`lia` tactic):

.. rocqtop:: in extra-stdlib

   From Stdlib Require Import Lia.
   Local Ltac2 lia_ltac1 () := ltac1:(lia).
   Ltac2 Notation "lia" := lia_ltac1 ().

A similar approach can be used to access missing built-in tactics.  See :ref:`simple_api` for an
example that passes two parameters to a missing build-in tactic.

.. _syntactic_classes:

Syntactic classes
~~~~~~~~~~~~~~~~~

The simplest syntactic classes in Ltac2 notations represent individual nonterminals
from the Rocq grammar.  Only a few selected nonterminals are available as syntactic classes.
In addition, there are metasyntactic operations for describing
more complex syntax, such as making an item optional or representing a list of items.
When parsing, each syntactic class expression returns a value that's bound to a name in the
notation definition.

Syntactic classes are described with a form of S-expression:

   .. insertprodn ltac2_scope ltac2_scope

   .. prodn::
      ltac2_scope ::= @string
      | @integer
      | @name
      | @name ( {+, @ltac2_scope } )

.. todo no syn class for ints or strings?
   parm names are not reserved (e.g the var can be named "list1")

Metasyntactic operations that can be applied to other syntactic classes are:

  :n:`opt(@ltac2_scope)`
    Parses an optional :token:`ltac2_scope`.  The associated value is either :n:`None` or
    enclosed in :n:`Some`

  :n:`list1(@ltac2_scope {? , @string })`
    Parses a list of one or more :token:`ltac2_scope`\s.  If :token:`string` is specified,
    items must be separated by :token:`string`.

  :n:`list0(@ltac2_scope {? , @string })`
    Parses a list of zero or more :token:`ltac2_scope`\s.  If :token:`string` is specified,
    items must be separated by :token:`string`.  For zero items, the associated value
    is an empty list.

  :n:`seq({+, @ltac2_scope })`
    Parses the :token:`ltac2_scope`\s in order.  The associated value is a tuple,
    omitting :token:`ltac2_scope`\s that are :token:`string`\s.
    `self` and `next` are not permitted within `seq`.

The following classes represent nonterminals with some special handling.  The
table further down lists the classes that that are handled plainly.

  :n:`constr {? ( {+, @scope_key } ) }`
    Parses a :token:`term`.  If specified, the :token:`scope_key`\s are used to interpret
    the term (as described in  :ref:`LocalInterpretationRulesForNotations`).  The last
    :token:`scope_key` is the top of the scope stack that's applied to the :token:`term`.

  :n:`open_constr {? ( {+, @scope_key } ) }`
    Parses an open :token:`term`. Like :n:`constr` above, this class
    accepts a list of notation scopes with the same effects.

.. _preterm:

  :n:`preterm {? ( {+, @scope_key } ) }`
    Parses a non-typechecked :token:`term`. Like :n:`constr` above, this class
    accepts a list of notation scopes with the same effects.

  :n:`ident`
    Parses :token:`ident` or :n:`$@ident`.  The first form returns :n:`ident:(@ident)`,
    while the latter form returns the variable :n:`@ident`.

  :n:`@string`
    Accepts the specified string that is not a keyword, returning a value of `()`.

  :n:`keyword(@string)`
    Accepts the specified string that is a keyword, returning a value of `()`.

  :n:`terminal(@string)`
    Accepts the specified string whether it's a keyword or not, returning a value of `()`.

  :n:`tactic {? (@integer) }`
    Parses an :token:`ltac2_expr`.  If :token:`integer` is specified, the construct
    parses a :n:`ltac2_expr@integer`, for example `tactic(5)` parses :token:`ltac2_expr5`.
    `tactic(6)` parses :token:`ltac2_expr`.
    :token:`integer` must be in the range `0 .. 6`.

    You can also use `tactic` to accept an :token:`integer` or a :token:`string`, but there's
    no syntactic class that accepts *only* an :token:`integer` or a :token:`string`.

    .. todo this doesn't work as expected: "::" is in ltac2_expr1
       Ltac2 Notation "ex4" x(tactic(0)) := x.
       ex4 auto :: [auto].

  .. not sure "self" and "next" do anything special.  I get the same error
     message for both from constructs like

     Ltac2 Notation "ex5" x(self) := auto.
     ex5 match.

     Syntax error: [tactic:tac2expr level 5] expected after 'match' (in [tactic:tac2expr]).

  :n:`self`
    parses an Ltac2 expression at the current level and returns it as is.

  :n:`next`
    parses an Ltac2 expression at the next level and returns it as is.

  :n:`thunk(@ltac2_scope)`
    Used for semantic effect only, parses the same as :token:`ltac2_scope`.
    If :n:`e` is the parsed expression for :token:`ltac2_scope`, `thunk`
    returns :n:`fun () => e`.

  :n:`pattern`
    parses a :token:`cpattern`

A few syntactic classes contain antiquotation features. For the sake of uniformity, all
antiquotations are introduced by the syntax :n:`$@lident`.

A few other specific syntactic classes exist to handle Ltac1-like syntax, but their use is
discouraged and they are thus not documented.

For now there is no way to declare new syntactic classes from the Ltac2 side, but this is
planned.

Other nonterminals that have syntactic classes are listed here.

   .. list-table::
      :header-rows: 1

      * - Syntactic class name
        - Nonterminal
        - Similar non-Ltac2 syntax

      * - :n:`intropatterns`
        - :token:`ltac2_intropatterns`
        - :n:`{* @intropattern }`

      * - :n:`intropattern`
        - :token:`ltac2_simple_intropattern`
        - :token:`simple_intropattern`

      * - :n:`ident`
        - :token:`ident_or_anti`
        - :token:`ident`

      * - :n:`destruction_arg`
        - :token:`ltac2_destruction_arg`
        - :token:`induction_arg`

      * - :n:`with_bindings`
        - :token:`q_with_bindings`
        - :n:`{? with @bindings }`

      * - :n:`bindings`
        - :token:`ltac2_bindings`
        - :token:`bindings`

      * - :n:`reductions`
        - :token:`ltac2_reductions`
        - :token:`reductions`

      * - :n:`reference`
        - :token:`refglobal`
        - :token:`reference`

      * - :n:`clause`
        - :token:`ltac2_clause`
        - :token:`occurrences`

      * - :n:`occurrences`
        - :token:`q_occurrences`
        - :n:`{? at @occs_nums }`

      * - :n:`induction_clause`
        - :token:`ltac2_induction_clause`
        - :token:`induction_clause`

      * - :n:`conversion`
        - :token:`ltac2_conversion`
        -

      * - :n:`orient`
        - :token:`q_orient`
        - :n:`{? {| -> | <- } }`

      * - :n:`rewriting`
        - :token:`ltac2_oriented_rewriter`
        - :token:`oriented_rewriter`

      * - :n:`dispatch`
        - :token:`ltac2_for_each_goal`
        - :token:`for_each_goal`

      * - :n:`hintdb`
        - :token:`hintdb`
        - :token:`hintbases`

      * - :n:`move_location`
        - :token:`move_location`
        - :token:`where`

      * - :n:`pose`
        - :token:`pose`
        - :token:`alias_definition`

      * - :n:`assert`
        - :token:`assertion`
        - :n:`( @ident := @term )`

      * - :n:`constr_matching`
        - :token:`ltac2_match_list`
        - See :tacn:`match`

      * - :n:`goal_matching`
        - :token:`goal_match_list`
        - See :tacn:`match goal`

Here is the syntax for the :n:`q_*` nonterminals:

.. insertprodn ltac2_intropatterns nonsimple_intropattern

.. prodn::
   ltac2_intropatterns ::= {* @nonsimple_intropattern }
   nonsimple_intropattern ::= *
   | **
   | @ltac2_simple_intropattern

.. insertprodn ltac2_simple_intropattern ltac2_equality_intropattern

.. prodn::
   ltac2_simple_intropattern ::= @ltac2_simple_intropattern_closed {* % @term0 }
   ltac2_simple_intropattern_closed ::= @ltac2_or_and_intropattern
   | @ltac2_equality_intropattern
   | _
   | @ltac2_naming_intropattern
   ltac2_naming_intropattern ::= ?@ident
   | ?$ @ident
   | ?
   | @ident_or_anti
   ltac2_or_and_intropattern ::= [ {+| @ltac2_intropatterns } ]
   | ()
   | ( {+, @ltac2_simple_intropattern } )
   | ( {+& @ltac2_simple_intropattern } )
   ltac2_equality_intropattern ::= ->
   | <-
   | [= @ltac2_intropatterns ]

.. insertprodn ident_or_anti ident_or_anti

.. prodn::
   ident_or_anti ::= @ident
   | $ @ident

.. insertprodn 	ltac2_destruction_arg ltac2_constr_with_bindings

.. prodn::
   ltac2_destruction_arg ::= @natural
   | @ident
   | @ltac2_constr_with_bindings
   ltac2_constr_with_bindings ::= @term {? with @ltac2_bindings }

.. insertprodn q_with_bindings qhyp

.. prodn::
   q_with_bindings ::= {? with @ltac2_bindings }
   ltac2_bindings ::= {+ @ltac2_simple_binding }
   | {+ @term }
   ltac2_simple_binding ::= ( @qhyp := @term )
   qhyp ::= $ @ident
   | @natural
   | @ident

.. insertprodn ltac2_reductions ltac2_delta_reductions

.. prodn::
   ltac2_reductions ::= {+ @ltac2_red_flag }
   | {? @ltac2_delta_reductions }
   ltac2_red_flag ::= beta
   | iota
   | match
   | fix
   | cofix
   | zeta
   | delta {? @ltac2_delta_reductions }
   | head
   ltac2_delta_reductions ::= {? - } [ {+ @refglobal } ]

.. insertprodn refglobal refglobal

.. prodn::
   refglobal ::= & @ident
   | @qualid
   | $ @ident

.. insertprodn ltac2_clause ltac2_in_clause

.. prodn::
   ltac2_clause ::= in @ltac2_in_clause
   | at @ltac2_occs_nums
   ltac2_in_clause ::= * {? @ltac2_occs }
   | * %|- {? @ltac2_concl_occ }
   | {*, @ltac2_hypident_occ } {? %|- {? @ltac2_concl_occ } }

.. insertprodn q_occurrences ltac2_hypident

.. prodn::
   q_occurrences ::= {? @ltac2_occs }
   ltac2_occs ::= at @ltac2_occs_nums
   ltac2_occs_nums ::= {? - } {+ {| @natural | $ @ident } }
   ltac2_concl_occ ::= * {? @ltac2_occs }
   ltac2_hypident_occ ::= @ltac2_hypident {? @ltac2_occs }
   ltac2_hypident ::= @ident_or_anti
   | ( type of @ident_or_anti )
   | ( value of @ident_or_anti )

.. insertprodn ltac2_induction_clause ltac2_eqn_ipat

.. prodn::
   ltac2_induction_clause ::= @ltac2_destruction_arg {? @ltac2_as_or_and_ipat } {? @ltac2_eqn_ipat } {? @ltac2_clause }
   ltac2_as_or_and_ipat ::= as @ltac2_or_and_intropattern
   ltac2_eqn_ipat ::= eqn : @ltac2_naming_intropattern

.. insertprodn ltac2_conversion ltac2_conversion

.. prodn::
   ltac2_conversion ::= @term
   | @term with @term

.. insertprodn q_rewriting ltac2_rewriter

.. prodn::
   q_rewriting ::= @ltac2_oriented_rewriter
   ltac2_oriented_rewriter ::= {? @q_orient } @ltac2_rewriter
   q_orient ::= {? {| -> | <- } }
   ltac2_rewriter ::= {? @natural } {? {| ? | ! } } @ltac2_constr_with_bindings

.. insertprodn ltac2_for_each_goal ltac2_goal_tactics

.. prodn::
   ltac2_for_each_goal ::= @ltac2_goal_tactics
   | {? @ltac2_goal_tactics %| } {? @ltac2_expr } .. {? %| @ltac2_goal_tactics }
   ltac2_goal_tactics ::= {*| {? @ltac2_expr } }

.. insertprodn hintdb hintdb

.. prodn::
   hintdb ::= *
   | {+ @ident_or_anti }

.. insertprodn move_location move_location

.. prodn::
   move_location ::= at top
   | at bottom
   | after @ident_or_anti
   | before @ident_or_anti

.. insertprodn pose ltac2_as_name

.. prodn::
   pose ::= ( @ident_or_anti := @term )
   | @term {? @ltac2_as_name }
   ltac2_as_name ::= as @ident_or_anti

.. insertprodn assertion ltac2_by_tactic

.. prodn::
   assertion ::= ( @ident_or_anti := @term )
   | ( @ident_or_anti : @term ) {? @ltac2_by_tactic }
   | @term {? @ltac2_as_ipat } {? @ltac2_by_tactic }
   ltac2_as_ipat ::= as @ltac2_simple_intropattern
   ltac2_by_tactic ::= by @ltac2_expr5

Evaluation
----------

Ltac2 features a toplevel loop that can be used to evaluate expressions.

.. cmd:: Ltac2 Eval @ltac2_expr

   This command evaluates the term in the current proof if there is one, or in the
   global environment otherwise, and displays the resulting value to the user
   together with its type. This command is pure in the sense that it does not
   modify the state of the proof, and in particular all side-effects are discarded.

Debug
-----

.. flag:: Ltac2 Backtrace

   When this :term:`flag` is set, toplevel failures will be printed with a backtrace.

Profiling
---------

.. flag:: Ltac2 In Ltac1 Profiling

   When this :term:`flag` and :flag:`Ltac Profiling` are set, profiling data is gathered for Ltac2 via the
   Ltac profiler. It is unset by default.

Compatibility layer with Ltac1
------------------------------

.. _ltac2in1:

Ltac1 from Ltac2
~~~~~~~~~~~~~~~~

.. _simple_api:

Simple API
++++++++++

One can call Ltac1 code from Ltac2 by using the :n:`ltac1:(@ltac1_expr_in_env)` quotation.
See :ref:`ltac2_built-in-quotations`.  It parses
a Ltac1 expression, and semantics of this quotation is the evaluation of the
corresponding code for its side effects. In particular, it cannot return values,
and the quotation has type :n:`unit`.

Ltac1 **cannot** implicitly access variables from the Ltac2 scope, but this can
be done with an explicit annotation on the :n:`ltac1:({* @ident } |- @ltac_expr)`
quotation.  See :ref:`ltac2_built-in-quotations`.  For example:

.. rocqtop:: in

   Local Ltac2 replace_with (lhs: constr) (rhs: constr) :=
     ltac1:(lhs rhs |- replace lhs with rhs) (Ltac1.of_constr lhs) (Ltac1.of_constr rhs).
   Ltac2 Notation "replace" lhs(constr) "with" rhs(constr) := replace_with lhs rhs.

The return type of this expression is a function of the same arity as the number
of identifiers, with arguments of type `Ltac2.Ltac1.t` (see below). This syntax
will bind the variables in the quoted Ltac1 code as if they had been bound from
Ltac1 itself. Similarly, the arguments applied to the quotation will be passed
at runtime to the Ltac1 code.

.. _low_level_api:

Low-level API
+++++++++++++

There exists a lower-level FFI into Ltac1 that is not recommended for daily use,
which is available in the `Ltac2.Ltac1` module. This API allows to directly
manipulate dynamically-typed Ltac1 values, either through the function calls,
or using the `ltac1val` quotation. The latter parses the same as `ltac1`, but
has type `Ltac2.Ltac1.t` instead of `unit`, and dynamically behaves as an Ltac1
thunk, i.e. `ltac1val:(foo)` corresponds to the tactic closure that Ltac1
would generate from `idtac; foo`.

Due to intricate dynamic semantics, understanding when Ltac1 value quotations
focus is very hard. This is why some functions return a continuation-passing
style value, as it can dispatch dynamically between focused and unfocused
behavior.

The same mechanism for explicit binding of variables as described in the
previous section applies.

Ltac2 from Ltac1
~~~~~~~~~~~~~~~~

Same as above by switching Ltac1 by Ltac2 and using the `ltac2` quotation
instead.

.. prodn::
   ltac_expr += ltac2 : ( @ltac2_expr )
   | ltac2 : ( {+ @ident } |- @ltac2_expr )

The typing rules are dual, that is, the optional identifiers are bound
with type `Ltac2.Ltac1.t` in the Ltac2 expression, which is expected to have
type unit. The value returned by this quotation is an Ltac1 function with the
same arity as the number of bound variables.

Note that when no variables are bound, the inner tactic expression is evaluated
eagerly, if one wants to use it as an argument to a Ltac1 function, one has to
resort to the good old :n:`idtac; ltac2:(foo)` trick. For instance, the code
below will fail immediately and won't print anything.

.. rocqtop:: in

   From Ltac2 Require Import Ltac2.
   Set Default Proof Mode "Classic".

.. rocqtop:: all

   Ltac mytac tac := idtac "I am being evaluated"; tac.

   Goal True.
   Proof.
   (* Doesn't print anything *)
   Fail mytac ltac2:(fail).
   (* Prints and fails *)
   Fail mytac ltac:(idtac; ltac2:(fail)).
   Abort.

In any case, the value returned by the fully applied quotation is an
unspecified dummy Ltac1 closure and should not be further used.

Use the `ltac2val` quotation to return values to Ltac1 from Ltac2.

.. prodn::
   ltac_expr += ltac2val : ( @ltac2_expr )
   | ltac2val : ( {+ @ident } |- @ltac2_expr )

It has the same typing rules as `ltac2:()` except the expression must have type `Ltac2.Ltac1.t`.

.. rocqtop:: all

   Import Constr.Unsafe.

   Ltac add1 x :=
     let f := ltac2val:(Ltac1.lambda (fun y =>
       let y := Option.get (Ltac1.to_constr y) in
       let y := make (App constr:(S) [|y|]) in
       Ltac1.of_constr y))
     in
     f x.

   Goal True.
     let z := constr:(0) in
     let v := add1 z in
     idtac v.
   Abort.

Switching between Ltac languages
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We recommend using the :opt:`Default Proof Mode` option or the :cmd:`Proof Mode`
command to switch between tactic languages.  The option has proof-level
granularity while the command has :term:`sentence`-level granularity. This
allows incrementally porting proof scripts.

Transition from Ltac1
---------------------

Owing to the use of a lot of notations, the transition should not be too
difficult. In particular, it should be possible to do it incrementally. That
said, we do *not* guarantee it will be a blissful walk either.
Hopefully, owing to the fact Ltac2 is typed, the interactive dialogue with the Rocq Prover
will help you.

We list the major changes and the transition strategies hereafter.

Syntax changes
~~~~~~~~~~~~~~

Due to conflicts, a few syntactic rules have changed.

- The dispatch tactical :n:`tac; [foo|bar]` is now written :n:`tac > [foo|bar]`.
- Levels of a few operators have been revised. Some tacticals now parse as if
  they were normal functions. Parentheses are now required around complex
  arguments, such as abstractions. The tacticals affected are:
  :n:`try`, :n:`repeat`, :n:`do`, :n:`once`, :n:`progress`, :n:`time`, :n:`abstract`.
- :n:`idtac` is no more. Either use :n:`()` if you expect nothing to happen,
  :n:`(fun () => ())` if you want a thunk (see next section), or use printing
  primitives from the :n:`Message` module if you want to display something.

Tactic delay
~~~~~~~~~~~~

Tactics are not magically delayed anymore, neither as functions nor as
arguments. It is your responsibility to thunk them beforehand and apply them
at the call site.

A typical example of a delayed function:

:n:`Ltac foo := blah.`

becomes

:n:`Ltac2 foo () := blah.`

All subsequent calls to `foo` must be applied to perform the same effect as
before.

Likewise, for arguments:

:n:`Ltac bar tac := tac; tac; tac.`

becomes

:n:`Ltac2 bar tac := tac (); tac (); tac ().`

We recommend the use of syntactic notations to ease the transition. For
instance, the first example can alternatively be written as:

:n:`Ltac2 foo0 () := blah.`
:n:`Ltac2 Notation foo := foo0 ().`

This allows to keep the subsequent calls to the tactic as-is, as the
expression `foo` will be implicitly expanded everywhere into `foo0 ()`. Such
a trick also works for arguments, as arguments of syntactic notations are
implicitly thunked. The second example could thus be written as follows.

:n:`Ltac2 bar0 tac := tac (); tac (); tac ().`
:n:`Ltac2 Notation bar := bar0.`

Variable binding
~~~~~~~~~~~~~~~~

Ltac1 relies on complex dynamic trickery to be able to tell apart bound
variables from terms, hypotheses, etc. There is no such thing in Ltac2,
as variables are recognized statically and other constructions do not live in
the same syntactic world. Due to the abuse of quotations, it can sometimes be
complicated to know what a mere identifier represents in a tactic expression. We
recommend tracking the context and letting the compiler print typing errors to
understand what is going on.

We list below the typical changes one has to perform depending on the static
errors produced by the typechecker.

In Ltac expressions
+++++++++++++++++++

.. exn:: Unbound {| value | constructor } X

   * if `X` is meant to be a term from the current static environment, replace
     the problematic use by `'X`.
   * if `X` is meant to be a hypothesis from the local context, replace the
     problematic use by `&X`.

In quotations
+++++++++++++

.. exn:: The reference X was not found in the current environment

   * if `X` is meant to be a tactic expression bound by a Ltac2 let or function,
     replace the problematic use by `$X`.
   * if `X` is meant to be a hypothesis from the local context, replace the
     problematic use by `&X`.

Exception catching
~~~~~~~~~~~~~~~~~~

Ltac2 features a proper exception-catching mechanism. For this reason, the
Ltac1 mechanism relying on `fail` taking integers, and tacticals decreasing it,
has been removed. Now exceptions are preserved by all tacticals, and it is
your duty to catch them and re-raise them as needed.
