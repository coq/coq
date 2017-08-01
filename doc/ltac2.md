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
  `(unit -> 'a) ~ unit -> ('a + (exn -> 'a))` i.e. thunks can produce a list
  of results waiting for failure exceptions.
- It can access a backtracking proof state, made out amongst other things of
  the current evar assignation and the list of goals under focus.

### Standard IO

The Ltac2 language features non-backtracking IO, notably mutable data and
printing operations.

Mutable fields of records can be modified using the set syntax

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
`plus "x" (fun () -> "y") : string` producing a backtracking string.

These operations are expected to satisfy a few equations, most notably that they
form a monoid compatible with sequentialization.

```
plus t zero ≡ t ()
plus (fun () -> zero e) f ≡ f e
plus (plus t f) g ≡ plus t (fun e -> plus (f e) g)

case (fun () -> zero e) ≡ Err e
case (fun () -> plus (fun () -> t) f) ≡ Val t f

let x := zero e in u ≡ fail e
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

A more expressive primitive allows to retrieve the data returned by each tactic
and store it in a list.

```
val enter_val : (unit -> 'a) -> 'a list
```

Accessing the goal data is then implicit in the Ltac2 primitives, and may fail
if the invariants are not respected. The two essential functions for observing
goals are given below.

```
val hyp : ident -> constr
val goal : unit -> constr
```

The two above functions fail if there is not exactly one goal under focus.
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

## Syntax example

Here is a suggestive example of a reasonable syntax.

```
let var := "H" in (* a string *)
let c := << fun $var$ => 0 >> (* the Coq term "fun H => 0" *)
let c' := << let x := $c$ in nat >> (* the Coq term "let x := fun H => 0 in nat" *)
...
```

## Term quotation

### Syntax

It is better to define primitively the quoting syntax to build terms, as this
is more robust to changes.

```
t, u ::= ... | << constr >>
```

The `constr` datatype have the same syntax as the usual Coq
terms, except that it also allows antiquotations of the form `$t$` whose type
is statically inferred from the position, e.g.

```
<< let $t$ := $u$ >> (** [t] is an ident, [u] is a constr *)
```

As the term syntax implicitly allows to inject other classes without marking,
antiquotations can refer explicitly to which class they belong to overcome this
limitation.

```
<< $ident:t$ >> (** [t] is an ident, and the corresponding constr is [GVar t] *)
<< $ref:t$ >> (** [t] is a reference, and the corresponding constr is [GRef t] *)
```

### Semantics

Interpretation of a quoted constr is done in two phases, internalization and
evaluation.
- During internalization, variables are resolved and antiquotations are
  type-checked as Ltac2 terms, effectively producing a `glob_constr` in Coq
  implementation terminology, potentially ill-typed as a Coq term.
- During evaluation, a quoted term is fully evaluated to a kernel term, and is
  in particular type-checked in the current environment.

Internalization is part of the static semantics, i.e. it is done at typing
time, while evaluation is part of the dynamic semantics, i.e. it is done when
a term gets effectively computed.

#### Static semantics

The typing rule of a quoted constr is given below, where the `eᵢ` refer to
antiquoted terms.

```
  Γ ⊢ e₁ : unit     Γ ⊢ eₙ : unit
====================================
  Γ ⊢ << c{$e₁$, ..., $eₙ$} >> : constr
```

Note that the **static** environment of typing of antiquotations is **not**
expanded by the binders from the term. Namely, it means that the following
expression will **not** type-check.
```
<< fun x : nat => $exact x$ >>
```

There is a simple reason for that, which is that the following expression would
not make sense in general.
```
<< fun x : nat => $clear x; exact x$ >>
```

Rather, the tactic writer has to resort to the **dynamic** environment, and must
write instead something that amounts to the following.
```
<< fun x : nat => $exact (hyp "x")$ >>
```

Obviously, we need to provide syntactic sugar to make this tractable. See the
corresponding section for more details.

#### Dynamic semantics

Evaluation of a quoted term is described below.
- The quoted term is evaluated by the pretyper.
- Antiquotations are evaluated in a context where there is exactly one goal
under focus, with the hypotheses coming from the current environment extended
with the bound variables of the term, and the resulting term is fed into the
quoted term.

Relative orders of evaluation of antiquotations and quoted term is not
specified.

## Patterns

Terms can be used in pattern position just as any Ltac constructor. The accepted
syntax is a subset of the constr syntax in Ltac term position, where
antiquotations are variables binding in the right-hand side.

Constructors and destructors can be derived from this. E.g. the previous
var-manipulating functions can be defined as follows.

```
let mkVar : ident -> constr = fun id -> << $ident:id$ >>

let destVar : constr -> ident = function
| << $ident:x$ >> -> x
| _ -> fail ()
```

One should be careful in patterns not to mix the syntax for evars with the one
for bound variables.

The usual match construction from Ltac1 can be derived from those primitive
operations. We should provide syntactic sugar to do so.

We need to decide how to handle bound variables in antiquotations, both in term
and pattern position. Should they bind? Should they not? What is the semantics
of the following snippet?

```
let foo = function << let x := t in $p$ >> -> p
let bar p = << let x := t in $p$ >>
```

What about the various kind of constrs? Untyped vs. typed, plus caring about
the context?

### Lists and Gallina `match`

It should be possible to manipulate Gallina `match` statements in a relatively
pain-free way.  For this reason, there should be a way to match on lists:

```
let replace_args = function << $f$ $a1 .. an$ >>
                            << $g$ $b1 .. bn$ >>
                -> << $f$ $b1 .. bn$ >>
let head = function << $f$ $a1 .. an$ >> -> << $f$ >>
let args : constr -> constr list = function << $f$ $a1 .. an$ >> -> [a1 ; .. ; an]
let apply (f : constr) : constr list -> constr = function
| $a1 .. an$ -> << $f$ $a1 .. an$ >>
let complicated_identity v = (let f = head v in let xs = args v in apply f xs)

let open_term_under_binders = function << fun $a1 .. an$ => $body$ >> -> << $body$ >>
let binders : constr -> ident list = function << fun $a1 .. an$ => $body$ >> -> [a1 ; .. ; an]
let close_term (body : constr) : ident list -> constr = function $a1 .. an$ -> << fun $a1 .. an$ => $body$ >>
let complicated_function_identity v =
  let b  = open_term_under_binders v in
  let xs = binders v                 in
  close_term body xs
```

We could implement the `@?P` pattern as something like the desugaring rule:
```
rule
  (match term with
   | (@?P a1 .. an))
  ~>
  let P = type_check (<< fun $a1 .. an$ => $term$ >>) in ...
```
The call to `type_check` ensures that there are no remaining holes in the term.
It is, perhaps, overkill.

Then we could destructure a `match` via syntax like:
```
let match_to_eta = function
| << match $t$ as $t'$ in $Ty$ return $P$ with
     | $c1$ => $v1$
     ..
     | $cm$ => $vm$
     end >>
  -> << match $t$ in $Ty$ return $Ty$ with
        | $c1$ => $c1$
        ..
        | $cm$ => $cm$
        end >>
```
which would take something like `match b with true => 0 | false => 1 end` and
return `match b with true => true | false => false end`.

We should be able to construct the eliminators for inductive types
in Ltac 2.0, using this syntax to generate the bodies, together with some
primitives for acquiring the relevant types.


**Questions**:
- What exactly are the semantics of `..`?
- Should it be `$a1 .. an$` or `$a1$ .. $an$`?
- This syntax suggests that when open terms are used in binding positions,
  unbound variables should become binding patterns.  That is, if you have
  `v` which has been constructed as `<< @cons _ $x$ $xs$ >>`, then
  `<< fun ls : list nat => match ls with $v$ => $v$ | _ => nil end >>` should
  be the eta-expansion of `ls`.  Is this desired semantics?  Are there issues
  with it?

# Notations

Notations are the crux of the usability of Ltac. We should be able to recover
a feeling similar to the old implementation by using and abusing notations.
This would be done at at level totally different from the semantics, which
is not what is happening as of today.

## Scopes

We would like to attach some scopes to identifiers, so that it could be possible
to write e.g.

```
Ltac intro : string -> unit := ...

Goal True -> True.
Proof.
intro "H". (** We require the quote here, as this is not a notation *)
Undo.
Top.intro "H". (** An alternative way, by fully qualifying the tactic *)
Abort.

Tactic Notation "intro" ident(i) := intro i.

Goal True -> True.
Proof.
intro H.
(** This sequence of tokens is elaborated at parsing time into [Top.intro "H"]
    thanks to the above notation. *)
Undo.
Top.intro "H".
(** Here, the core tactic is still reachable using the fully qualified name *)
Abort.
```

A typical notation that would be useful is the Coq term one, so that the
following is possible.

```
Ltac destruct : constr -> unit := ...

Tactic Notation "destruct" constr(x) := destruct x.

Goal False -> True.
Proof.
intro H. (** assuming we have the previous notation in scope *)
destruct H. (** H is interpreted in the current goal? *)
Undo.
Top.destruct << H >> (** alternative without notation *)
```

Another one, probably useful for transition, would be a scope `legacy_constr`
that parses an identifier s.t. `legacy_constr(H)` elaborates to
`hyp H + mkVar H`.

One should be able to define new scopes, by giving them a qualified name,
a old scope used for the parsing rule, and an expansion macro. We can maybe
unify such a scope creation process with the tactic notation one?

## Syntactic sugar

A few dedicated syntaxes should be built-in into Ltac2 for easy manipulation
of Coq-specific data.

### Identifiers

We need to write identifiers as easily as strings. What about `#foo` standing
for the identifier `foo`?

### Hypotheses

We need to be able to access easily a hypothesis from its name. What about
`` `foo `` being a shorthand for `hyp "foo"`? This needs to be accessible inside
terms as well.

# Transition path

TODO
