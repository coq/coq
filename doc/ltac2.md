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

## Overview

Ltac2 is a member of the ML family of languages, in the sense that it is an
effectful call-by-value functional language, with static typing à la
Hindley-Milner. It is commonly accepted that ML constitutes a sweet spot in PL
design, as it is relatively expressive while not being either too lax
(contrarily to dynamic typing) nor too strict (contrarily to say, dependent
types).

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
| "[" ".." "]"

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
statically defined, but can instead be extended dynamically. A typical example
is the standard `exn` type. Pattern-matching must always include a catch-all
clause. They can be extended by the following command.

```
VERNAC ::=
| "Ltac2" "Type" TYPEPARAMS QUALID ":=" "[" CONSTRUCTORDEF "]"
```

## Term Syntax

The syntax of the functional fragment is very close to the one of Ltac1, except
that it adds a true pattern-matching feature, as well as a few standard
constructions from ML.

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
| "Ltac2" MUTFLAG RECFLAG LIDENT ":=" TERM
```

For semantic reasons, the body of the Ltac2 definition must be a syntactical
value, i.e. a function, a constant or a pure constructor recursively applied to
values.

If the `RECFLAG` is set, the tactic is expanded into a recursive binding.

If the `MUTFLAG` is set, the definition can be redefined at a later stage. This
can be performed through the following command.

```
VERNAC ::=
| "Ltac2" "Set" QUALID ":=" TERM
```

Mutable definitions act like dynamic binding, i.e. at runtime, the last defined
value for this entry is chosen. This is useful for global flags and the like.

## Reduction

We use the usual ML call-by-value reduction, with an otherwise unspecified
evaluation order. This is a design choice making it compatible with OCaml,
if ever we implement native compilation. The expected equations are as follows.
```
(fun x => t) V ≡ t{x := V} (βv)

let x := V in t ≡ t{x := V} (let)

match C V₀ ... Vₙ with ... | C x₀ ... xₙ  => t | ... end ≡ t {xᵢ := Vᵢ} (ι)

(t any term, V values, C constructor)
```

Note that call-by-value reduction is already a departure from Ltac1 which uses
heuristics to decide when evaluating an expression. For instance, the following
expressions do not evaluate the same way in Ltac1.

```
foo (idtac; let x := 0 in bar)

foo (let x := 0 in bar)
```

Instead of relying on the `idtac` hack, we would now require an explicit thunk
not to compute the argument, and `foo` would have e.g. type
`(unit -> unit) -> unit`.

```
foo (fun () => let x := 0 in bar)
```

## Typing

Typing is strict and follows Hindley-Milner system. We will not implement the
current hackish subtyping semantics, and one will have to resort to conversion
functions. See notations though to make things more palatable. 

In this setting, all usual argument-free tactics have type `unit -> unit`, but
one can return as well a value of type `t` thanks to terms of type `unit -> t`,
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

We describe more thoroughly the various effects existing in Ltac2 hereafter.

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
`plus (fun () => "x") (fun _ => "y") : string` producing a backtracking string.

These operations are expected to satisfy a few equations, most notably that they
form a monoid compatible with sequentialization.

```
plus t zero ≡ t ()
plus (fun () => zero e) f ≡ f e
plus (plus t f) g ≡ plus t (fun e => plus (f e) g)

case (fun () => zero e) ≡ Err e
case (fun () => plus (fun () => t) f) ≡ Val t f

let x := zero e in u ≡ zero e
let x := plus t f in u ≡ plus (fun () => let x := t in u) (fun e => let x := f e in u)

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

### Built-in quotations

The current implementation recognizes the following built-in quotations:
- "ident", which parses identifiers (type `Init.ident`).
- "constr", which parses Coq terms and produces an-evar free term at runtime
  (type `Init.constr`).
- "open_constr", which parses Coq terms and produces a term potentially with
  holes at runtime (type `Init.constr` as well).
- "pattern", which parses Coq patterns and produces a pattern used for term
  matching (type `Init.pattern`).
- "reference", which parses either a `QUALID` or `"&" IDENT`. Qualified names
  are globalized at internalization into the corresponding global reference,
  while `&id` is turned into `Std.VarRef id`. This produces at runtime a
  `Std.reference`.

The following syntactic sugar is provided for two common cases.
- `@id` is the same as ident:(id)
- `'t` is the same as open_constr:(t)

### Strict vs. non-strict mode

Depending on the context, quotations producing terms (i.e. `constr` or
`open_constr`) are not internalized in the same way. There are two possible
modes, respectively called the *strict* and the *non-strict* mode.

- In strict mode, all simple identifiers appearing in a term quotation are
required to be resolvable statically. That is, they must be the short name of
a declaration which is defined globally, excluding section variables and
hypotheses. If this doesn't hold, internalization will fail. To work around
this error, one has to specifically use the `&` notation.
- In non-strict mode, any simple identifier appearing in a term quotation which
is not bound in the global context is turned into a dynamic reference to a
hypothesis. That is to say, internalization will succeed, but the evaluation
of the term at runtime will fail if there is no such variable in the dynamic
context.

Strict mode is enforced by default, e.g. for all Ltac2 definitions. Non-strict
mode is only set when evaluating Ltac2 snippets in interactive proof mode. The
rationale is that it is cumbersome to explicitly add `&` interactively, while it
is expected that global tactics enforce more invariants on their code.

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

Remark that typing of Coq terms is a *dynamic* process occuring at Ltac2
evaluation time, and not at Ltac2 typing time.

#### Static semantics

During internalization, Coq variables are resolved and antiquotations are
type-checked as Ltac2 terms, effectively producing a `glob_constr` in Coq
implementation terminology. Note that although it went through the
type-checking of **Ltac2**, the resulting term has not been fully computed and
is potentially ill-typed as a runtime **Coq** term.

```
Ltac2 Definition myconstr () := constr:(nat -> 0).
// Valid with type `unit -> constr`, but will fail at runtime.
```

Term antiquotations are type-checked in the enclosing Ltac2 typing context
of the corresponding term expression. For instance, the following will
type-check.

```
let x := '0 in constr:(1 + ltac2:(exact x))
// type constr
```

Beware that the typing environment of typing of antiquotations is **not**
expanded by the Coq binders from the term. Namely, it means that the following
Ltac2 expression will **not** type-check.
```
constr:(fun x : nat => ltac2:(exact x))
// Error: Unbound variable 'x'
```

There is a simple reason for that, which is that the following expression would
not make sense in general.
```
constr:(fun x : nat => ltac2:(clear @x; exact x))
```
Indeed, a hypothesis can suddenly disappear from the runtime context if some
other tactic pulls the rug from under you.

Rather, the tactic writer has to resort to the **dynamic** goal environment,
and must write instead explicitly that she is accessing a hypothesis, typically
as follows.
```
constr:(fun x : nat => ltac2:(exact (hyp @x)))
```

This pattern is so common that we provide dedicated Ltac2 and Coq term notations
for it.

- `&x` as an Ltac2 expression expands to `hyp @x`.
- `&x` as a Coq constr expression expands to
  `ltac2:(Control.refine (fun () => hyp @x))`.

#### Dynamic semantics

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
whole expression will thus evaluate to the term `fun H : nat => nat`.
```
let tac () := hyp @H in constr:(fun H : nat => ltac2:(tac ()))
```

Many standard tactics perform type-checking of their argument before going
further. It is your duty to ensure that terms are well-typed when calling
such tactics. Failure to do so will result in non-recoverable exceptions.

## Trivial Term Antiquotations

It is possible to refer to a variable of type `constr` in the Ltac2 environment
through a specific syntax consistent with the antiquotations presented in
the notation section.

```
COQCONSTR ::=
| "$" LIDENT
```

In a Coq term, writing `$x` is semantically equivalent to
`ltac2:(Control.refine (fun () => x))`, up to re-typechecking. It allows to
insert in a concise way an Ltac2 variable of type `constr` into a Coq term.

## Match over terms

Ltac2 features a construction similar to Ltac1 `match` over terms, although
in a less hard-wired way.

```
TERM ::=
| "match!" TERM "with" CONSTR-MATCHING* "end"
| "lazy_match!" TERM "with" CONSTR-MATCHING* "end"
| "multi_match!" TERM "with" CONSTR-MATCHING*"end"

CONSTR-MATCHING :=
| "|" CONSTR-PATTERN "=>" TERM

CONSTR-PATTERN :=
| CONSTR
| "context" LIDENT? "[" CONSTR "]"
```

This construction is not primitive and is desugared at parsing time into
calls to term matching functions from the `Pattern` module. Internally, it is
implemented thanks to a specific scope accepting the `CONSTR-MATCHING` syntax.

Variables from the `CONSTR-PATTERN` are statically bound in the body of the branch, to
values of type `constr` for the variables from the `CONSTR` pattern and to a
value of type `Pattern.context` for the variable `LIDENT`.

Note that contrarily to Ltac, only lowercase identifiers are valid as Ltac2
bindings, so that there will be a syntax error if one of the bound variables
starts with an uppercase character.

The semantics of this construction is otherwise the same as the corresponding
one from Ltac1, except that it requires the goal to be focussed.

## Match over goals

Similarly, there is a way to match over goals in an elegant way, which is
just a notation desugared at parsing time.

```
TERM ::=
| "match!" MATCH-ORDER? "goal" "with" GOAL-MATCHING* "end"
| "lazy_match!" MATCH-ORDER? "goal" "with" GOAL-MATCHING* "end"
| "multi_match!" MATCH-ORDER? "goal" "with" GOAL-MATCHING*"end"

GOAL-MATCHING :=
| "|" "[" HYP-MATCHING* "|-" CONSTR-PATTERN "]" "=>" TERM

HYP-MATCHING :=
| LIDENT ":" CONSTR-PATTERN

MATCH-ORDER :=
| "reverse"
```

Variables from `HYP-MATCHING` and `CONSTR-PATTERN` are bound in the body of the
branch. Their types are:
- `constr` for pattern variables appearing in a `CONSTR`
- `Pattern.context` for variables binding a context
- `ident` for variables binding a hypothesis name.

The same identifier caveat as in the case of matching over constr applies, and
this features has the same semantics as in Ltac1. In particular, a `reverse`
flag can be specified to match hypotheses from the more recently introduced to
the least recently introduced one.

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
  + parses the same as *scope*, and if *e* is the parsed expression, returns
  `fun () => e`.
- STRING:
  + parses the corresponding string as a CAMLP5 IDENT and returns `()`.
- keyword(s = STRING):
  + parses the string *s* as a keyword and returns `()`.
- terminal(s = STRING):
  + parses the string *s* as a keyword, if it is already a
    keyword, otherwise as an IDENT. Returns `()`.
- seq(*scope₁*, ..., *scopeₙ*):
  + parses *scope₁*, ..., *scopeₙ* in this order, and produces a tuple made
    out of the parsed values in the same order. As an optimization, all
    subscopes of the form STRING are left out of the returned tuple, instead
    of returning a useless unit value. It is forbidden for the various
    subscopes to refer to the global entry using self of next.

A few other specific scopes exist to handle Ltac1-like syntax, but their use is
discouraged and they are thus not documented.

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
let y := @X in foo (nat -> nat) x $y
```
will expand at parsing time to
```
let y := @X in
let c := fun () => constr:(nat -> nat) with ids := [@x; y] in Bar.f c ids
```

Beware that the order of evaluation of multiple let-bindings is not specified,
so that you may have to resort to thunking to ensure that side-effects are
performed at the right time.

## Abbreviations

There exists a special kind of notations, called abbreviations, that is designed
so that it does not add any parsing rules. It is similar in spirit to Coq
abbreviations, insofar as its main purpose is to give an absolute name to a
piece of pure syntax, which can be transparently referred by this name as if it
were a proper definition. Abbreviations are introduced by the following
syntax.

```
VERNAC ::=
| "Ltac2" "Notation" IDENT ":=" TERM
```

The abbreviation can then be manipulated just as a normal Ltac2 definition,
except that it is expanded at internalization time into the given expression.
Furthermore, in order to make this kind of construction useful in practice in
an effectful language such as Ltac2, any syntactic argument to an abbreviation
is thunked on-the-fly during its expansion.

For instance, suppose that we define the following.
```
Ltac2 Notation foo := fun x => x ().
```
Then we have the following expansion at internalization time.
```
foo 0 ↦ (fun x => x ()) (fun _ => 0)
```

Note that abbreviations are not typechecked at all, and may result in typing
errors after expansion.

# Evaluation

Ltac2 features a toplevel loop that can be used to evaluate expressions.

```
VERNAC ::=
| "Ltac2" "Eval" TERM
```

This command evaluates the term in the current proof if there is one, or in the
global environment otherwise, and displays the resulting value to the user
together with its type. This function is pure in the sense that it does not
modify the state of the proof, and in particular all side-effects are discarded.

# Debug

When the option `Ltac2 Backtrace` is set, toplevel failures will be printed with
a backtrace.

# Compatibility layer with Ltac1

## Ltac1 from Ltac2

One can call Ltac1 code from Ltac2 by using the `ltac1` quotation. It parses
a Ltac1 expression, and semantics of this quotation is the evaluation of the
corresponding code for its side effects. In particular, in cannot return values,
and the quotation has type `unit`.

Beware, Ltac1 **cannot** access variables from the Ltac2 scope. One is limited
to the use of standalone function calls.

## Ltac2 from Ltac1

Same as above by switching Ltac1 by Ltac2 and using the `ltac2` quotation
instead.

Note that the tactic expression is evaluated eagerly, if one wants to use it as
an argument to a Ltac1 function, she has to resort to the good old
`idtac; ltac2:(foo)` trick. For instance, the code below will fail immediately
and won't print anything.

```
Ltac mytac tac := idtac "wow"; tac.

Goal True.
Proof.
mytac ltac2:(fail).
```

# Transition from Ltac1

Owing to the use of a bunch of notations, the transition shouldn't be
atrociously horrible and shockingly painful up to the point you want to retire
in the Ariège mountains, living off the land and insulting careless bypassers in
proto-georgian.

That said, we do *not* guarantee you it is going to be a blissful walk either.
Hopefully, owing to the fact Ltac2 is typed, the interactive dialogue with Coq
will help you.

We list the major changes and the transition strategies hereafter.

## Syntax changes

Due to conflicts, a few syntactic rules have changed.

- The dispatch tactical `tac; [foo|bar]` is now written `tac > [foo|bar]`.
- Levels of a few operators have been revised. Some tacticals now parse as if
  they were a normal function, i.e. one has to put parentheses around the
  argument when it is complex, e.g an abstraction. List of affected tacticals:
  `try`, `repeat`, `do`, `once`, `progress`, `time`, `abstract`.
- `idtac` is no more. Either use `()` if you expect nothing to happen,
  `(fun () => ())` if you want a thunk (see next section), or use printing
  primitives from the `Message` module if you want to display something.

## Tactic delay

Tactics are not magically delayed anymore, neither as functions nor as
arguments. It is your responsibility to thunk them beforehand and apply them
at the call site.

A typical example of a delayed function:
```
Ltac foo := blah.
```
becomes
```
Ltac2 foo () := blah.
```

All subsequent calls to `foo` must be applied to perform the same effect as
before.

Likewise, for arguments:
```
Ltac bar tac := tac; tac; tac.
```
becomes
```
Ltac2 bar tac := tac (); tac (); tac ().
```

We recommend the use of syntactic notations to ease the transition. For
instance, the first example can alternatively written as:
```
Ltac2 foo0 () := blah.
Ltac2 Notation foo := foo0 ().
```

This allows to keep the subsequent calls to the tactic as-is, as the
expression `foo` will be implicitly expanded everywhere into `foo0 ()`. Such
a trick also works for arguments, as arguments of syntactic notations are
implicitly thunked. The second example could thus be written as follows.

```
Ltac2 bar0 tac := tac (); tac (); tac ().
Ltac2 Notation bar := bar0.
```

## Variable binding

Ltac1 relies on a crazy amount of dynamic trickery to be able to tell apart
bound variables from terms, hypotheses and whatnot. There is no such thing in
Ltac2, as variables are recognized statically and other constructions do not
live in the same syntactic world. Due to the abuse of quotations, it can
sometimes be complicated to know what a mere identifier represents in a tactic
expression. We recommend tracking the context and letting the compiler spit
typing errors to understand what is going on.

We list below the typical changes one has to perform depending on the static
errors produced by the typechecker.

### In Ltac expressions

- `Unbound value X`, `Unbound constructor X`:
  * if `X` is meant to be a term from the current stactic environment, replace
    the problematic use by `'X`.
  * if `X` is meant to be a hypothesis from the goal context, replace the
    problematic use by `&X`.

### In quotations

- `The reference X was not found in the current environment`:
  * if `X` is meant to be a tactic expression bound by a Ltac2 let or function,
    replace the problematic use by `$X`.
  * if `X` is meant to be a hypothesis from the goal context, replace the
    problematic use by `&X`.

## Exception catching

Ltac2 features a proper exception-catching mechanism. For this reason, the
Ltac1 mechanism relying on `fail` taking integers and tacticals decreasing it
has been removed. Now exceptions are preserved by all tacticals, and it is
your duty to catch it and reraise it depending on your use.

# TODO

- Implement deep pattern-matching.
- Craft an expressive set of primitive functions
- Implement native compilation to OCaml
