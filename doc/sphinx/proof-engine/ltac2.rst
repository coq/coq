.. _ltac2:

.. coqtop:: none

   From Ltac2 Require Import Ltac2.

Ltac2
=====

The Ltac tactic language is probably one of the ingredients of the success of
Coq, yet it is at the same time its Achilles' heel. Indeed, Ltac:

- has often unclear semantics
- is very non-uniform due to organic growth
- lacks expressivity (data structures, combinators, types, ...)
- is slow
- is error-prone and fragile
- has an intricate implementation

Following the need of users that start developing huge projects relying
critically on Ltac, we believe that we should offer a proper modern language
that features at least the following:

- at least informal, predictable semantics
- a typing system
- standard programming facilities (i.e. datatypes)

This new language, called Ltac2, is described in this chapter. It is still
experimental but we encourage nonetheless users to start testing it,
especially wherever an advanced tactic language is needed. The previous
implementation of Ltac, described in the previous chapter, will be referred to
as Ltac1.

.. _ltac2_design:

General design
--------------

There are various alternatives to Ltac1, such that Mtac or Rtac for instance.
While those alternatives can be quite distinct from Ltac1, we designed
Ltac2 to be closest as reasonably possible to Ltac1, while fixing the
aforementioned defects.

In particular, Ltac2 is:

- a member of the ML family of languages, i.e.

  * a call-by-value functional language
  * with effects
  * together with Hindley-Milner type system

- a language featuring meta-programming facilities for the manipulation of
  Coq-side terms
- a language featuring notation facilities to help writing palatable scripts

We describe more in details each point in the remainder of this document.

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

The main goal of Ltac2 is to serve as a meta-language for Coq. As such, it
naturally fits in the ML lineage, just as the historical ML was designed as
the tactic language for the LCF prover. It can also be seen as a general-purpose
language, by simply forgetting about the Coq-specific features.

Sticking to a standard ML type system can be considered somewhat weak for a
meta-language designed to manipulate Coq terms. In particular, there is no
way to statically guarantee that a Coq term resulting from an Ltac2
computation will be well-typed. This is actually a design choice, motivated
by retro-compatibility with Ltac1. Instead, well-typedness is deferred to
dynamic checks, allowing many primitive functions to fail whenever they are
provided with an ill-typed term.

The language is naturally effectful as it manipulates the global state of the
proof engine. This allows to think of proof-modifying primitives as effects
in a straightforward way. Semantically, proof manipulation lives in a monad,
which allows to ensure that Ltac2 satisfies the same equations as a generic ML
with unspecified effects would do, e.g. function reduction is substitution
by a value.

Type Syntax
~~~~~~~~~~~

At the level of terms, we simply elaborate on Ltac1 syntax, which is quite
close to e.g. the one of OCaml. Types follow the simply-typed syntax of OCaml.

The non-terminal :production:`lident` designates identifiers starting with a
lowercase.

.. productionlist:: coq
   ltac2_type             : ( `ltac2_type`, ... , `ltac2_type` ) `ltac2_typeconst`
                    : ( `ltac2_type` * ... * `ltac2_type` )
                    : `ltac2_type` -> `ltac2_type`
                    : `ltac2_typevar`
   ltac2_typeconst        : ( `modpath` . )* `lident`
   ltac2_typevar          : '`lident`
   ltac2_typeparams       : ( `ltac2_typevar`, ... , `ltac2_typevar` )

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

One can define new types by the following commands.

.. cmd:: Ltac2 Type {? @ltac2_typeparams } @lident
   :name: Ltac2 Type

   This command defines an abstract type. It has no use for the end user and
   is dedicated to types representing data coming from the OCaml world.

.. cmdv:: Ltac2 Type {? rec} {? @ltac2_typeparams } @lident := @ltac2_typedef

   This command defines a type with a manifest. There are four possible
   kinds of such definitions: alias, variant, record and open variant types.

   .. productionlist:: coq
      ltac2_typedef    : `ltac2_type`
                       : [ `ltac2_constructordef` | ... | `ltac2_constructordef` ]
                       : { `ltac2_fielddef` ; ... ; `ltac2_fielddef` }
                       : [ .. ]
      ltac2_constructordef   : `uident` [ ( `ltac2_type` , ... , `ltac2_type` ) ]
      ltac2_fielddef         : [ mutable ] `ident` : `ltac2_type`

   Aliases are just a name for a given type expression and are transparently
   unfoldable to it. They cannot be recursive. The non-terminal
   :production:`uident` designates identifiers starting with an uppercase.

   Variants are sum types defined by constructors and eliminated by
   pattern-matching. They can be recursive, but the `rec` flag must be
   explicitly set. Pattern-maching must be exhaustive.

   Records are product types with named fields and eliminated by projection.
   Likewise they can be recursive if the `rec` flag is set.

   .. cmdv:: Ltac2 Type {? @ltac2_typeparams } @ltac2_qualid ::= [ @ltac2_constructordef ]

      Open variants are a special kind of variant types whose constructors are not
      statically defined, but can instead be extended dynamically. A typical example
      is the standard `exn` type. Pattern-matching must always include a catch-all
      clause. They can be extended by this command.

Term Syntax
~~~~~~~~~~~

The syntax of the functional fragment is very close to the one of Ltac1, except
that it adds a true pattern-matching feature, as well as a few standard
constructions from ML.

.. productionlist:: coq
   ltac2_var        : `lident`
   ltac2_qualid     : ( `modpath` . )* `lident`
   ltac2_constructor: `uident`
   ltac2_term       : `ltac2_qualid`
                    : `ltac2_constructor`
                    : `ltac2_term` `ltac2_term` ... `ltac2_term`
                    : fun `ltac2_var` => `ltac2_term`
                    : let `ltac2_var` := `ltac2_term` in `ltac2_term`
                    : let rec `ltac2_var` := `ltac2_term` in `ltac2_term`
                    : match `ltac2_term` with `ltac2_branch` ... `ltac2_branch` end
                    : `integer`
                    : `string`
                    : `ltac2_term` ; `ltac2_term`
                    : [| `ltac2_term` ; ... ; `ltac2_term` |]
                    : ( `ltac2_term` , ... , `ltac2_term` )
                    : { `ltac2_field` `ltac2_field` ... `ltac2_field` }
                    : `ltac2_term` . ( `ltac2_qualid` )
                    : `ltac2_term` . ( `ltac2_qualid` ) := `ltac2_term`
                    : [; `ltac2_term` ; ... ; `ltac2_term` ]
                    : `ltac2_term` :: `ltac2_term`
                    : ...
   ltac2_branch     : `ltac2_pattern` => `ltac2_term`
   ltac2_pattern    : `ltac2_var`
                    : _
                    : ( `ltac2_pattern` , ... , `ltac2_pattern` )
                    : `ltac2_constructor` `ltac2_pattern` ... `ltac2_pattern`
                    : [ ]
                    : `ltac2_pattern` :: `ltac2_pattern`
   ltac2_field      : `ltac2_qualid` := `ltac2_term`

In practice, there is some additional syntactic sugar that allows e.g. to
bind a variable and match on it at the same time, in the usual ML style.

There is a dedicated syntax for list and array literals.

.. note::

   For now, deep pattern matching is not implemented.

Ltac Definitions
~~~~~~~~~~~~~~~~

.. cmd:: Ltac2 {? mutable} {? rec} @lident := @ltac2_term
   :name: Ltac2

   This command defines a new global Ltac2 value.

   For semantic reasons, the body of the Ltac2 definition must be a syntactical
   value, i.e. a function, a constant or a pure constructor recursively applied to
   values.

   If ``rec`` is set, the tactic is expanded into a recursive binding.

   If ``mutable`` is set, the definition can be redefined at a later stage (see below).

.. cmd:: Ltac2 Set @qualid := @ltac2_term
   :name: Ltac2 Set

   This command redefines a previous ``mutable`` definition.
   Mutable definitions act like dynamic binding, i.e. at runtime, the last defined
   value for this entry is chosen. This is useful for global flags and the like.

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
heuristics to decide when evaluating an expression. For instance, the following
expressions do not evaluate the same way in Ltac1.

:n:`foo (idtac; let x := 0 in bar)`

:n:`foo (let x := 0 in bar)`

Instead of relying on the :n:`idtac` idiom, we would now require an explicit thunk
not to compute the argument, and :n:`foo` would have e.g. type
:n:`(unit -> unit) -> unit`.

:n:`foo (fun () => let x := 0 in bar)`

Typing
~~~~~~

Typing is strict and follows Hindley-Milner system. Unlike Ltac1, there
are no type casts at runtime, and one has to resort to conversion
functions. See notations though to make things more palatable.

In this setting, all usual argument-free tactics have type :n:`unit -> unit`, but
one can return as well a value of type :n:`t` thanks to terms of type :n:`unit -> t`,
or take additional arguments.

Effects
~~~~~~~

Effects in Ltac2 are straightforward, except that instead of using the
standard IO monad as the ambient effectful world, Ltac2 is going to use the
tactic monad.

Note that the order of evaluation of application is *not* specified and is
implementation-dependent, as in OCaml.

We recall that the `Proofview.tactic` monad is essentially a IO monad together
with backtracking state representing the proof state.

Intuitively a thunk of type :n:`unit -> 'a` can do the following:

- It can perform non-backtracking IO like printing and setting mutable variables
- It can fail in a non-recoverable way
- It can use first-class backtrack. The proper way to figure that is that we
  morally have the following isomorphism:
  :n:`(unit -> 'a) ~ (unit -> exn + ('a * (exn -> 'a)))`
  i.e. thunks can produce a lazy list of results where each
  tail is waiting for a continuation exception.
- It can access a backtracking proof state, made out amongst other things of
  the current evar assignation and the list of goals under focus.

We describe more thoroughly the various effects existing in Ltac2 hereafter.

Standard IO
+++++++++++

The Ltac2 language features non-backtracking IO, notably mutable data and
printing operations.

Mutable fields of records can be modified using the set syntax. Likewise,
built-in types like `string` and `array` feature imperative assignment. See
modules `String` and `Array` respectively.

A few printing primitives are provided in the `Message` module, allowing to
display information to the user.

Fatal errors
++++++++++++

The Ltac2 language provides non-backtracking exceptions, also known as *panics*,
through the following primitive in module `Control`.::

  val throw : exn -> 'a

Unlike backtracking exceptions from the next section, this kind of error
is never caught by backtracking primitives, that is, throwing an exception
destroys the stack. This is materialized by the following equation, where `E`
is an evaluation context.::

  E[throw e] ≡ throw e

  (e value)

There is currently no way to catch such an exception and it is a design choice.
There might be at some future point a way to catch it in a brutal way,
destroying all backtrack and return values.

Backtrack
+++++++++

In Ltac2, we have the following backtracking primitives, defined in the
`Control` module.::

  Ltac2 Type 'a result := [ Val ('a) | Err (exn) ].

  val zero : exn -> 'a
  val plus : (unit -> 'a) -> (exn -> 'a) -> 'a
  val case : (unit -> 'a) -> ('a * (exn -> 'a)) result

If one sees thunks as lazy lists, then `zero` is the empty list and `plus` is
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
to a given goal. This is the role of the `enter` primitive, that applies a
tactic to each currently focused goal in turn.::

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
not ``foo`` applied to the Ltac integer expression ``0`` (Ltac does have a
notion of integers, though it is not first-class), but rather the Coq term
:g:`Datatypes.O`.

The implicit parsing is confusing to users and often gives unexpected results.
Ltac2 makes these explicit using quoting and unquoting notation, although there
are notations to do it in a short and elegant way so as not to be too cumbersome
to the user.

Generic Syntax for Quotations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In general, quotations can be introduced in terms using the following syntax, where
:production:`quotentry` is some parsing entry.

.. prodn::
   ltac2_term += @ident : ( @quotentry )

Built-in quotations
+++++++++++++++++++

The current implementation recognizes the following built-in quotations:

- ``ident``, which parses identifiers (type ``Init.ident``).
- ``constr``, which parses Coq terms and produces an-evar free term at runtime
  (type ``Init.constr``).
- ``open_constr``, which parses Coq terms and produces a term potentially with
  holes at runtime (type ``Init.constr`` as well).
- ``pattern``, which parses Coq patterns and produces a pattern used for term
  matching (type ``Init.pattern``).
- ``reference``, which parses either a :n:`@qualid` or :n:`& @ident`. Qualified names
  are globalized at internalization into the corresponding global reference,
  while ``&id`` is turned into ``Std.VarRef id``. This produces at runtime a
  ``Std.reference``.

The following syntactic sugar is provided for two common cases.

- ``@id`` is the same as ``ident:(id)``
- ``'t`` is the same as ``open_constr:(t)``

Strict vs. non-strict mode
++++++++++++++++++++++++++

Depending on the context, quotations producing terms (i.e. ``constr`` or
``open_constr``) are not internalized in the same way. There are two possible
modes, respectively called the *strict* and the *non-strict* mode.

- In strict mode, all simple identifiers appearing in a term quotation are
  required to be resolvable statically. That is, they must be the short name of
  a declaration which is defined globally, excluding section variables and
  hypotheses. If this doesn't hold, internalization will fail. To work around
  this error, one has to specifically use the ``&`` notation.
- In non-strict mode, any simple identifier appearing in a term quotation which
  is not bound in the global context is turned into a dynamic reference to a
  hypothesis. That is to say, internalization will succeed, but the evaluation
  of the term at runtime will fail if there is no such variable in the dynamic
  context.

Strict mode is enforced by default, e.g. for all Ltac2 definitions. Non-strict
mode is only set when evaluating Ltac2 snippets in interactive proof mode. The
rationale is that it is cumbersome to explicitly add ``&`` interactively, while it
is expected that global tactics enforce more invariants on their code.

Term Antiquotations
~~~~~~~~~~~~~~~~~~~

Syntax
++++++

One can also insert Ltac2 code into Coq terms, similarly to what is possible in
Ltac1.

.. prodn::
   term += ltac2:( @ltac2_term )

Antiquoted terms are expected to have type ``unit``, as they are only evaluated
for their side-effects.

Semantics
+++++++++

Interpretation of a quoted Coq term is done in two phases, internalization and
evaluation.

- Internalization is part of the static semantics, i.e. it is done at Ltac2
  typing time.
- Evaluation is part of the dynamic semantics, i.e. it is done when
  a term gets effectively computed by Ltac2.

Note that typing of Coq terms is a *dynamic* process occurring at Ltac2
evaluation time, and not at Ltac2 typing time.

Static semantics
****************

During internalization, Coq variables are resolved and antiquotations are
type-checked as Ltac2 terms, effectively producing a ``glob_constr`` in Coq
implementation terminology. Note that although it went through the
type-checking of **Ltac2**, the resulting term has not been fully computed and
is potentially ill-typed as a runtime **Coq** term.

.. example::

   The following term is valid (with type `unit -> constr`), but will fail at runtime:

   .. coqtop:: in

      Ltac2 myconstr () := constr:(nat -> 0).

Term antiquotations are type-checked in the enclosing Ltac2 typing context
of the corresponding term expression.

.. example::

   The following will type-check, with type `constr`.

   .. coqdoc::

      let x := '0 in constr:(1 + ltac2:(exact x))

Beware that the typing environment of antiquotations is **not**
expanded by the Coq binders from the term.

  .. example::

     The following Ltac2 expression will **not** type-check::

     `constr:(fun x : nat => ltac2:(exact x))`
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

This pattern is so common that we provide dedicated Ltac2 and Coq term notations
for it.

- `&x` as an Ltac2 expression expands to `hyp @x`.
- `&x` as a Coq constr expression expands to
  `ltac2:(Control.refine (fun () => hyp @x))`.

Dynamic semantics
*****************

During evaluation, a quoted term is fully evaluated to a kernel term, and is
in particular type-checked in the current environment.

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

Many standard tactics perform type-checking of their argument before going
further. It is your duty to ensure that terms are well-typed when calling
such tactics. Failure to do so will result in non-recoverable exceptions.

**Trivial Term Antiquotations**

It is possible to refer to a variable of type `constr` in the Ltac2 environment
through a specific syntax consistent with the antiquotations presented in
the notation section.

.. prodn:: term += $@lident

In a Coq term, writing :g:`$x` is semantically equivalent to
:g:`ltac2:(Control.refine (fun () => x))`, up to re-typechecking. It allows to
insert in a concise way an Ltac2 variable of type :n:`constr` into a Coq term.

Match over terms
~~~~~~~~~~~~~~~~

Ltac2 features a construction similar to Ltac1 :n:`match` over terms, although
in a less hard-wired way.

.. productionlist:: coq
   ltac2_term       : match! `ltac2_term` with `constrmatching` .. `constrmatching` end
                    : lazy_match! `ltac2_term` with `constrmatching` .. `constrmatching` end
                    : multi_match! `ltac2_term` with `constrmatching` .. `constrmatching` end
   constrmatching  : | `constrpattern` => `ltac2_term`
   constrpattern   : `term`
                   : context  [ `term` ]
                   : context `lident` [ `term` ]

This construction is not primitive and is desugared at parsing time into
calls to term matching functions from the `Pattern` module. Internally, it is
implemented thanks to a specific scope accepting the :n:`@constrmatching` syntax.

Variables from the :n:`@constrpattern` are statically bound in the body of the branch, to
values of type `constr` for the variables from the :n:`@term` pattern and to a
value of type `Pattern.context` for the variable :n:`@lident`.

Note that unlike Ltac, only lowercase identifiers are valid as Ltac2
bindings, so that there will be a syntax error if one of the bound variables
starts with an uppercase character.

The semantics of this construction is otherwise the same as the corresponding
one from Ltac1, except that it requires the goal to be focused.

Match over goals
~~~~~~~~~~~~~~~~

Similarly, there is a way to match over goals in an elegant way, which is
just a notation desugared at parsing time.

.. productionlist:: coq
   ltac2_term             : match! [ reverse ] goal with `goalmatching` ... `goalmatching` end
                    : lazy_match! [ reverse ] goal with `goalmatching` ... `goalmatching` end
                    : multi_match! [ reverse ] goal with `goalmatching` ... `goalmatching` end
   goalmatching     : | [ `hypmatching` ... `hypmatching` |- `constrpattern` ] => `ltac2_term`
   hypmatching      : `lident` : `constrpattern`
                    : _ : `constrpattern`

Variables from :n:`@hypmatching` and :n:`@constrpattern` are bound in the body of the
branch. Their types are:

- ``constr`` for pattern variables appearing in a :n:`@term`
- ``Pattern.context`` for variables binding a context
- ``ident`` for variables binding a hypothesis name.

The same identifier caveat as in the case of matching over constr applies, and
this features has the same semantics as in Ltac1. In particular, a ``reverse``
flag can be specified to match hypotheses from the more recently introduced to
the least recently introduced one.

.. _ltac2_notations:

Notations
---------

Notations are the crux of the usability of Ltac1. We should be able to recover
a feeling similar to the old implementation by using and abusing notations.

Scopes
~~~~~~

A scope is a name given to a grammar entry used to produce some Ltac2 expression
at parsing time. Scopes are described using a form of S-expression.

.. prodn::
   ltac2_scope ::= {| @string | @integer | @lident ({+, @ltac2_scope}) }

A few scopes contain antiquotation features. For sake of uniformity, all
antiquotations are introduced by the syntax :n:`$@lident`.

The following scopes are built-in.

- :n:`constr`:

  + parses :n:`c = @term` and produces :n:`constr:(c)`

  This scope can be parameterized by a list of delimiting keys of interpretation
  scopes (as described in :ref:`LocalInterpretationRulesForNotations`),
  describing how to interpret the parsed term. For instance, :n:`constr(A, B)`
  parses :n:`c = @term` and produces :n:`constr:(c%A%B)`.

- :n:`ident`:

  + parses :n:`id = @ident` and produces :n:`ident:(id)`
  + parses :n:`$(x = @ident)` and produces the variable :n:`x`

- :n:`list0(@ltac2_scope)`:

  + if :n:`@ltac2_scope` parses :n:`@quotentry`,
    then it parses :n:`(@quotentry__0, ..., @quotentry__n)` and produces
    :n:`[@quotentry__0; ...; @quotentry__n]`.

- :n:`list0(@ltac2_scope, sep = @string__sep)`:

  + if :n:`@ltac2_scope` parses :n:`@quotentry`,
    then it parses :n:`(@quotentry__0 @string__sep ... @string__sep @quotentry__n)`
    and produce :n:`[@quotentry__0; ...; @quotentry__n]`.

- :n:`list1`: same as :n:`list0` (with or without separator) but parses :n:`{+ @quotentry}` instead
  of :n:`{* @quotentry}`.

- :n:`opt(@ltac2_scope)`

  + if :n:`@ltac2_scope` parses :n:`@quotentry`, parses :n:`{? @quotentry}` and produces either :n:`None` or
    :n:`Some x` where :n:`x` is the parsed expression.

- :n:`self`:

  + parses a Ltac2 expression at the current level and return it as is.

- :n:`next`:

  + parses a Ltac2 expression at the next level and return it as is.

- :n:`tactic(n = @integer)`:

  + parses a Ltac2 expression at the provided level :n:`n` and return it as is.

- :n:`thunk(@ltac2_scope)`:

  + parses the same as :n:`scope`, and if :n:`e` is the parsed expression, returns
    :n:`fun () => e`.

- :n:`STRING`:

  + parses the corresponding string as an identifier and returns :n:`()`.

- :n:`keyword(s = @string)`:

  + parses the string :n:`s` as a keyword and returns `()`.

- :n:`terminal(s = @string)`:

  + parses the string :n:`s` as a keyword, if it is already a
    keyword, otherwise as an :n:`@ident`. Returns `()`.

- :n:`seq(@ltac2_scope__1, ..., @ltac2_scope__2)`:

  + parses :n:`scope__1`, ..., :n:`scope__n` in this order, and produces a tuple made
    out of the parsed values in the same order. As an optimization, all
    subscopes of the form :n:`STRING` are left out of the returned tuple, instead
    of returning a useless unit value. It is forbidden for the various
    subscopes to refer to the global entry using self or next.

A few other specific scopes exist to handle Ltac1-like syntax, but their use is
discouraged and they are thus not documented.

For now there is no way to declare new scopes from Ltac2 side, but this is
planned.

Notations
~~~~~~~~~

The Ltac2 parser can be extended by syntactic notations.

.. cmd:: Ltac2 Notation {+ {| @lident (@ltac2_scope) | @string } } {? : @integer} := @ltac2_term
   :name: Ltac2 Notation

   A Ltac2 notation adds a parsing rule to the Ltac2 grammar, which is expanded
   to the provided body where every token from the notation is let-bound to the
   corresponding generated expression.

   .. example::

      Assume we perform:

      .. coqdoc::

         Ltac2 Notation "foo" c(thunk(constr)) ids(list0(ident)) := Bar.f c ids.

      Then the following expression

      `let y := @X in foo (nat -> nat) x $y`

      will expand at parsing time to

      `let y := @X in`
      `let c := fun () => constr:(nat -> nat) with ids := [@x; y] in Bar.f c ids`

      Beware that the order of evaluation of multiple let-bindings is not specified,
      so that you may have to resort to thunking to ensure that side-effects are
      performed at the right time.

Abbreviations
~~~~~~~~~~~~~

.. cmdv:: Ltac2 Notation @lident := @ltac2_term

  This command introduces a special kind of notations, called abbreviations,
  that is designed so that it does not add any parsing rules. It is similar in
  spirit to Coq abbreviations, insofar as its main purpose is to give an
  absolute name to a piece of pure syntax, which can be transparently referred
  by this name as if it were a proper definition.

  The abbreviation can then be manipulated just as a normal Ltac2 definition,
  except that it is expanded at internalization time into the given expression.
  Furthermore, in order to make this kind of construction useful in practice in
  an effectful language such as Ltac2, any syntactic argument to an abbreviation
  is thunked on-the-fly during its expansion.

For instance, suppose that we define the following.

:n:`Ltac2 Notation foo := fun x => x ().`

Then we have the following expansion at internalization time.

:n:`foo 0 ↦ (fun x => x ()) (fun _ => 0)`

Note that abbreviations are not typechecked at all, and may result in typing
errors after expansion.

Evaluation
----------

Ltac2 features a toplevel loop that can be used to evaluate expressions.

.. cmd:: Ltac2 Eval @ltac2_term
   :name: Ltac2 Eval

   This command evaluates the term in the current proof if there is one, or in the
   global environment otherwise, and displays the resulting value to the user
   together with its type. This command is pure in the sense that it does not
   modify the state of the proof, and in particular all side-effects are discarded.

Debug
-----

.. flag:: Ltac2 Backtrace

   When this flag is set, toplevel failures will be printed with a backtrace.

Compatibility layer with Ltac1
------------------------------

Ltac1 from Ltac2
~~~~~~~~~~~~~~~~

Simple API
++++++++++

One can call Ltac1 code from Ltac2 by using the :n:`ltac1` quotation. It parses
a Ltac1 expression, and semantics of this quotation is the evaluation of the
corresponding code for its side effects. In particular, it cannot return values,
and the quotation has type :n:`unit`.

Ltac1 **cannot** implicitly access variables from the Ltac2 scope, but this can
be done via an explicit annotation to the :n:`ltac1` quotation.

.. productionlist:: coq
  ltac2_term : ltac1 : ( `ident` ... `ident` |- `ltac_expr` )

The return type of this expression is a function of the same arity as the number
of identifiers, with arguments of type `Ltac2.Ltac1.t` (see below). This syntax
will bind the variables in the quoted Ltac1 code as if they had been bound from
Ltac1 itself. Similarly, the arguments applied to the quotation will be passed
at runtime to the Ltac1 code.

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
behaviour.

The same mechanism for explicit binding of variables as described in the
previous section applies.

Ltac2 from Ltac1
~~~~~~~~~~~~~~~~

Same as above by switching Ltac1 by Ltac2 and using the `ltac2` quotation
instead.

Note that the tactic expression is evaluated eagerly, if one wants to use it as
an argument to a Ltac1 function, she has to resort to the good old
:n:`idtac; ltac2:(foo)` trick. For instance, the code below will fail immediately
and won't print anything.

.. coqtop:: in

   From Ltac2 Require Import Ltac2.
   Set Default Proof Mode "Classic".

.. coqtop:: all

   Ltac mytac tac := idtac "wow"; tac.

   Goal True.
   Proof.
   Fail mytac ltac2:(fail).

Transition from Ltac1
---------------------

Owing to the use of a lot of notations, the transition should not be too
difficult. In particular, it should be possible to do it incrementally. That
said, we do *not* guarantee you it is going to be a blissful walk either.
Hopefully, owing to the fact Ltac2 is typed, the interactive dialogue with Coq
will help you.

We list the major changes and the transition strategies hereafter.

Syntax changes
~~~~~~~~~~~~~~

Due to conflicts, a few syntactic rules have changed.

- The dispatch tactical :n:`tac; [foo|bar]` is now written :n:`tac > [foo|bar]`.
- Levels of a few operators have been revised. Some tacticals now parse as if
  they were a normal function, i.e. one has to put parentheses around the
  argument when it is complex, e.g an abstraction. List of affected tacticals:
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

   * if `X` is meant to be a term from the current stactic environment, replace
     the problematic use by `'X`.
   * if `X` is meant to be a hypothesis from the goal context, replace the
     problematic use by `&X`.

In quotations
+++++++++++++

.. exn:: The reference X was not found in the current environment

   * if `X` is meant to be a tactic expression bound by a Ltac2 let or function,
     replace the problematic use by `$X`.
   * if `X` is meant to be a hypothesis from the goal context, replace the
     problematic use by `&X`.

Exception catching
~~~~~~~~~~~~~~~~~~

Ltac2 features a proper exception-catching mechanism. For this reason, the
Ltac1 mechanism relying on `fail` taking integers, and tacticals decreasing it,
has been removed. Now exceptions are preserved by all tacticals, and it is
your duty to catch them and reraise them depending on your use.
