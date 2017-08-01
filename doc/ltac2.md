# Summary

The Ltac tactic language is probably one of the ingredients of the success of
Coq, yet it is at the same time its Achilles' heel. Indeed, Ltac:

- has nothing like intended semantics
- is very non-uniform due to organic growth
- lacks expressivity and requires programming-by-hacking
- is slow
- is error-prone and fragile
- has an intricate implementation

This has a lot of terrible consequences, most notably the fact that it is never
clear whether some observed behaviour is a bug or a proper one.

Following the need of users that start developing huge projects relying 
critically on Ltac, we believe that we should offer a proper modern language
that features at least the following:

- at least informal, predictible semantics
- a typing system
- standard programming facilities (i.e. datatypes)

This document describes the implementation of such a language. The
implementation of Ltac as of Coq 8.7 will be referred to as Ltac1.

# General design

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

# ML component

The call-by-value functional language fragment is easy to implement.

## Type Syntax

At the level of terms, we simply elaborate on Ltac1 syntax, which is quite
close to e.g. the one of OCaml. Types follow the simply-typed syntax of OCaml.

```
TYPE :=
| "(" TYPE₀ "," ... "," TYPEₙ ")" TYPECONST
| "(" TYPE₀ "*" ... "*" TYPEₙ ")"
| TYPE₁ "->" TYPE₂
| TYPEVAR

TYPECONST := ( MODPATH "." )* LIDENT

TYPEVAR := "'" LIDENT

TYPEPARAMS := "(" TYPEVAR₀ "," ... "," TYPEVARₙ ")"
```

The set of base types can be extended thanks to the usual ML type
declarations such as algebraic datatypes and records.

Built-in types include:
- `int`, machine integers (size not specified, in practice inherited from OCaml)
- `string`, mutable strings
- `'a array`, mutable arrays
- `exn`, exceptions
- `constr`, kernel-side terms
- `pattern`, term patterns
- `ident`, well-formed identifiers

## Type declarations

One can define new types by the following commands.

```
VERNAC ::=
| "Ltac2" "Type" TYPEPARAMS LIDENT
| "Ltac2" "Type" RECFLAG TYPEPARAMS LIDENT ":=" TYPEDEF

RECFLAG := ( "rec" )
```

The first command defines an abstract type. It has no use for the end user and
is dedicated to types representing data coming from the OCaml world.

The second command defines a type with a manifest. There are four possible
kinds of such definitions: alias, variant, record and open variant types.

```
TYPEDEF :=
| TYPE
| "[" CONSTRUCTORDEF₀ "|" ... "|" CONSTRUCTORDEFₙ "]"
| "{" FIELDDEF₀ ";" ... ";" FIELDDEFₙ "}"
| "[" "..." "]"

CONSTRUCTORDEF :=
| IDENT ( "(" TYPE₀ "," ... "," TYPE₀ ")" )

FIELDDEF :=
| MUTFLAG IDENT ":" TYPE

MUTFLAG := ( "mutable" )
```

Aliases are just a name for a given type expression and are transparently
unfoldable to it. They cannot be recursive.

Variants are sum types defined by constructors and eliminated by
pattern-matching. They can be recursive, but the `RECFLAG` must be explicitly
set. Pattern-maching must be exhaustive.

Records are product types with named fields and eliminated by projection.
Likewise they can be recursive if the `RECFLAG` is set.

Open variants are a special kind of variant types whose constructors are not
statically defined, but can instead by extended dynamically. A typical example
is the standard `exn` type. Pattern-matching must always include a catch-all
clause. They can be extended by the following command.

```
VERNAC ::=
| "Ltac2" "Type" TYPEPARAMS QUALID ":=" "[" CONSTRUCTORDEF "]"
```

## Term Syntax

The syntax of the functional fragment is very close to the one of Ltac1, except
that it adds a true pattern-matching feature.

```
VAR := LIDENT

QUALID := ( MODPATH "." )* LIDENT

CONSTRUCTOR := UIDENT

TERM :=
| QUALID
| CONSTRUCTOR TERM₀ ... TERMₙ
| TERM TERM₀ ... TERMₙ
| "fun" VAR "=>" TERM
| "let" VAR ":=" TERM "in" TERM
| "let" "rec" VAR ":=" TERM "in" TERM
| "match" TERM "with" BRANCH* "end"
| INT
| STRING
| "[|" TERM₀ ";" ... ";" TERMₙ "|]"
| "(" TERM₀ "," ... "," TERMₙ ")"
| "{" FIELD+ "}"
| TERM "." "(" QUALID ")"
| TERM₁ "." "(" QUALID ")" ":=" TERM₂
| "["; TERM₀ ";" ... ";" TERMₙ "]"
| TERM₁ "::" TERM₂
| ...

BRANCH :=
| PATTERN "=>" TERM

PATTERN :=
| VAR
| "_"
| "(" PATTERN₀ "," ... "," PATTERNₙ ")"
| CONSTRUCTOR PATTERN₀ ... PATTERNₙ
| "[" "]"
| PATTERN₁ "::" PATTERN₂

FIELD :=
| QUALID ":=" TERM

```

In practice, there is some additional syntactic sugar that allows e.g. to
bind a variable and match on it at the same time, in the usual ML style.

There is a dedicated syntax for list and array litterals.

Limitations: for now, deep pattern matching is not implemented yet.

## Ltac Definitions

One can define a new global Ltac2 value using the following syntax.
```
VERNAC ::=
| "Ltac2" RECFLAG LIDENT ":=" TERM
```

For semantic reasons, the body of the Ltac2 definition must be a syntactical
value, i.e. a function, a constant or a pure constructor recursively applied to
values.

If the `RECFLAG` is set, the tactic is expanded into a recursive binding.

## Reduction

We use the usual ML call-by-value reduction, with an otherwise unspecified
evaluation order.

Note that this is already a departure from Ltac1 which uses heuristic to
decide when evaluating an expression, e.g. the following do not evaluate the
same way.

```
foo (idtac; let x := 0 in bar)

foo (let x := 0 in bar)
```

Instead of relying on the `idtac` hack, we would now require an explicit thunk
not to compute the argument, and `foo` would have e.g. type
`(unit -> unit) -> unit`.

```
foo (fun () -> let x := 0 in bar)
```

## Typing

Typing is strict and follows Hindley-Milner system. We will not implement the
current hackish subtyping semantics, and one will have to resort to conversion
functions. See notations though to make things more palatable. 

In this setting, all usual argument-free tactics have type `unit -> unit`, but
one can return as well a value of type `τ` thanks to terms of type `unit -> τ`,
or take additional arguments.

## Effects

Regarding effects, nothing involved here, except that instead of using the
standard IO monad as the ambient effectful world, Ltac2 is going to use the
tactic monad.

Note that the order of evaluation of application is *not* specified and is
implementation-dependent, as in OCaml.

We recall that the `Proofview.tactic` monad is essentially a IO monad together
with backtracking state representing the proof state.

Intuitively a thunk of type `unit -> 'a` can do the following:
- It can perform non-backtracking IO like printing and setting mutable variables
- It can fail in a non-recoverable way
- It can use first-class backtrack. The proper way to figure that is that we
  morally have the following isomorphism:
  `(unit -> 'a) ~ (unit -> exn + ('a * (exn -> 'a)))` i.e. thunks can produce a
  lazy list of results where each tail is waiting for a continuation exception.
- It can access a backtracking proof state, made out amongst other things of
  the current evar assignation and the list of goals under focus.

### Standard IO

The Ltac2 language features non-backtracking IO, notably mutable data and
printing operations.

Mutable fields of records can be modified using the set syntax. Likewise,
built-in types like `string` and `array` feature imperative assignment. See
modules `String` and `Array` respectively.

A few printing primitives are provided in the `Message` module, allowing to
display information to the user.

### Fatal errors

The Ltac2 language provides non-backtracking exceptions through the
following primitive in module `Control`.

```
val throw : exn -> 'a
```

Contrarily to backtracking exceptions from the next section, this kind of error
is never caught by backtracking primitives, that is, throwing an exception
destroys the stack. This is materialized by the following equation, where `E`
is an evaluation context.

```
E[throw e] ≡ throw e

(e value)
```

There is currently no way to catch such an exception and it is a design choice.
There might be at some future point a way to catch it in a brutal way,
destroying all backtrack and return values.

### Backtrack

In Ltac2, we have the following backtracking primitives, defined in the
`Control` module.

```
Ltac2 Type 'a result := [ Val ('a) | Err (exn) ].

val zero : exn -> 'a
val plus : (unit -> 'a) -> (exn -> 'a) -> 'a
val case : (unit -> 'a) -> ('a * (exn -> 'a)) result
```

If one sees thunks as lazy lists, then `zero` is the empty list and `plus` is
list concatenation, while `case` is pattern-matching.

The backtracking is first-class, i.e. one can write
`plus "x" (fun () => "y") : string` producing a backtracking string.

These operations are expected to satisfy a few equations, most notably that they
form a monoid compatible with sequentialization.

```
plus t zero ≡ t ()
plus (fun () -> zero e) f ≡ f e
plus (plus t f) g ≡ plus t (fun e -> plus (f e) g)

case (fun () -> zero e) ≡ Err e
case (fun () -> plus (fun () -> t) f) ≡ Val t f

let x := zero e in u ≡ zero e
let x := plus t f in u ≡ plus (fun () -> let x := t in u) (fun e -> let x := f e in u)

(t, u, f, g, e values)
```

### Goals

A goal is given by the data of its conclusion and hypotheses, i.e. it can be
represented as `[Γ ⊢ A]`.

The tactic monad naturally operates over the whole proofview, which may
represent several goals, including none. Thus, there is no such thing as
*the current goal*. Goals are naturally ordered, though.

It is natural to do the same in Ltac2, but we must provide a way to get access
to a given goal. This is the role of the `enter` primitive, that applies a
tactic to each currently focussed goal in turn.

```
val enter : (unit -> unit) -> unit
```

It is guaranteed that when evaluating `enter f`, `f` is called with exactly one
goal under focus. Note that `f` may be called several times, or never, depending
on the number of goals under focus before the call to `enter`.

Accessing the goal data is then implicit in the Ltac2 primitives, and may panic
if the invariants are not respected. The two essential functions for observing
goals are given below.

```
val hyp : ident -> constr
val goal : unit -> constr
```

The two above functions panic if there is not exactly one goal under focus.
In addition, `hyp` may also fail if there is no hypothesis with the
corresponding name.

# Meta-programming

## Overview

One of the horrendous implementation issues of Ltac is the fact that it is
never clear whether an object refers to the object world or the meta-world.
This is an incredible source of slowness, as the interpretation must be
aware of bound variables and must use heuristics to decide whether a variable
is a proper one or referring to something in the Ltac context.

Likewise, in Ltac1, constr parsing is implicit, so that `foo 0` is
not `foo` applied to the Ltac integer expression `0` (Ltac does have a
non-first-class notion of integers), but rather the Coq term `Datatypes.O`.

We should stop doing that! We need to mark when quoting and unquoting, although
we need to do that in a short and elegant way so as not to be too cumbersome
to the user.

## Generic Syntax for Quotations

In general, quotations can be introduced in term by the following syntax, where
`QUOTENTRY` is some parsing entry.
```
TERM ::=
| QUOTNAME ":" "(" QUOTENTRY ")"

QUOTNAME := IDENT
```

The current implementation recognizes the following built-in quotations:
- "ident", which parses identifiers (type `Init.ident`).
- "constr", which parses Coq terms and produces an-evar free term at runtime
  (type `Init.constr`).
- "open_constr", which parses Coq terms and produces a term potentially with
  holes at runtime (type `Init.constr` as well).
- "pattern", which parses Coq patterns and produces a pattern used for term
  matching (type `Init.pattern`).

The following syntactic sugar is provided for two common cases.
- `@id` is the same as ident:(id)
- `'t` is the same as open_constr:(t)

## Term Antiquotations

### Syntax

One can also insert Ltac2 code into Coq term, similarly to what was possible in
Ltac1.

```
COQCONSTR ::=
| "ltac2" ":" "(" TERM ")"
```

Antiquoted terms are expected to have type `unit`, as they are only evaluated
for their side-effects.

### Semantics

Interpretation of a quoted Coq term is done in two phases, internalization and
evaluation.

- Internalization is part of the static semantics, i.e. it is done at Ltac2
  typing time.
- Evaluation is part of the dynamic semantics, i.e. it is done when
  a term gets effectively computed by Ltac2.

#### Static semantics

During internalization, Coq variables are resolved and antiquotations are
type-checked as Ltac2 terms, effectively producing a `glob_constr` in Coq
implementation terminology. Note that although it went through the
type-checking of *Ltac2*, the resulting term has not been fully computed and
is potentially ill-typed as a Coq term.

```
Ltac2 Definition myconstr () := constr:(nat -> 0).
// Valid with type `unit -> constr`, but will fail at runtime.
```

Term antiquotations are type-checked in the enclosing Ltac2 typing context
of the corresponding term expression. For instance, the following with
type-check.

```
let x := '0 in constr:(1 + ltac2:(exact x))
// type constr
```

Beware that the typing environment of typing of antiquotations is **not**
expanded by the Coq binders from the term. Namely, it means that the following
expression will **not** type-check.
```
constr:(fun x : nat => ltac2:(exact x))
// Error: Unbound variable 'x'
```

There is a simple reason for that, which is that the following expression would
not make sense in general.
```
constr:(fun x : nat => ltac2:(clear @x; exact x))
```

Rather, the tactic writer has to resort to the **dynamic** goal environment,
and must write instead explicitly that she is accessing a hypothesis, typically
as follows.
```
constr:(fun x : nat => ltac2:(hyp @x))
```

The `ltac2:(hyp @x)` pattern is so common that we provide a dedicated Coq
term notation for it.

#### Dynamic semantics

During evaluation, a quoted term is fully evaluated to a kernel term, and is
in particular type-checked in the current environment.

Evaluation of a quoted term is described below.
- The quoted term is evaluated by the pretyper.
- Antiquotations are evaluated in a context where there is exactly one goal
under focus, with the hypotheses coming from the current environment extended
with the bound variables of the term, and the resulting term is fed into the
quoted term.

Relative orders of evaluation of antiquotations and quoted term is not
specified.

For instance, in the following example, `tac` will be evaluated in a context
with exactly one goal under focus, whose last hypothesis is `H : nat`. The
whole expression will thus evaluate to the term `fun H : nat => nat`.
```
let tac () := hyp @H in constr:(fun H : nat => ltac2:(tac ()))
```

Many standard tactics perform type-checking of their argument before going
further. It is your duty to ensure that terms are well-typed when calling
such tactics. Failure to do so will result in non-recoverable exceptions.

## Patterns

Terms can be used in pattern position just as any Ltac constructor. The accepted
syntax is a subset of the constr syntax in Ltac term position. It does not
allow antiquotations.

Patterns quotations are typically used with the matching functions provided
in the `Pattern` module.

# Notations

Notations are the crux of the usability of Ltac1. We should be able to recover
a feeling similar to the old implementation by using and abusing notations.

## Scopes

A scope is a name given to a grammar entry used to produce some Ltac2 expression
at parsing time. Scopes are described using a form of S-expression.

```
SCOPE :=
| STRING
| INT
| LIDENT ( "(" SCOPE₀ "," ... "," SCOPEₙ ")" )
```

A few scopes contain antiquotation features. For sake of uniformity, all
antiquotations are introduced by the syntax `"$" VAR`.

The following scopes are built-in.
- constr:
  + parses `c = COQCONSTR` and produces `constr:(c)`
- ident:
  + parses `id = IDENT` and produces `ident:(id)`
  + parses `"$" (x = IDENT)` and produces the variable `x`
- list0(*scope*):
  + if *scope* parses `ENTRY`, parses ̀`(x₀, ..., xₙ = ENTRY*)` and produces
    `[x₀; ...; xₙ]`.
- list0(*scope*, sep = STRING):
  + if *scope* parses `ENTRY`, parses `(x₀ = ENTRY, "sep", ..., "sep", xₙ = ENTRY)`
    and produces `[x₀; ...; xₙ]`.
- list1: same as list0 (with or without separator) but parses `ENTRY+` instead
  of `ENTRY*`.
- opt(*scope*)
  + if *scope* parses `ENTRY`, parses `ENTRY?` and produces either `None` or
    `Some x` where `x` is the parsed expression.
- self:
  + parses a Ltac2 expression at the current level and return it as is.
- next:
  + parses a Ltac2 expression at the next level and return it as is.
- tactic(n = INT):
  + parses a Ltac2 expression at the provided level *n* and return it as is.
- thunk(*scope*):
  parses the same as *scope*, and if *e* is the parsed expression, returns
  `fun () => e`.

For now there is no way to declare new scopes from Ltac2 side, but this is
planned.

## Notations

The Ltac2 parser can be extended by syntactic notations.
```
VERNAC ::=
| "Ltac2" "Notation" TOKEN+ LEVEL? ":=" TERM

LEVEL := ":" INT

TOKEN :=
| VAR "(" SCOPE ")"
| STRING
```

A Ltac2 notation adds a parsing rule to the Ltac2 grammar, which is expanded
to the provided body where every token from the notation is let-bound to the
corresponding generated expression.

For instance, assume we perform:
```
Ltac2 Notation "foo" c(thunk(constr)) ids(list0(ident)) := Bar.f c ids.
```
Then the following expression
```
let y := @X in foo (nat -> nat) x ?y
```
will expand at parsing time to
```
let y := @X in
let c := fun () => constr:(nat -> nat) with ids := [@x; y] in Bar.f c ids
```

Beware that the order of evaluation of multiple let-bindings is not specified,
so that you may have to resort to thunking to ensure that side-effects are
performed at the right time.
