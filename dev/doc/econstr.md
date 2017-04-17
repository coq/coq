# Evar-insensitive terms (EConstr)

Evar-insensitive terms were introduced in 8.7, following
[CEP #10](https://github.com/coq/ceps/blob/master/text/010-econstr.md). We will
not recap the motivations in this document and rather summarize the code changes
to perform.

## Overview

The essential datastructures are defined in
[the `EConstr` module](/engine/eConstr.mli) module. It defines
the tactic counterparts of kernel data structures such as terms
(`EConstr.constr`), universes (`EConstr.ESorts.t`) and contexts
(`EConstr.*_context`).

The main difference with kernel-side types is that observing them requires
an evar-map at hand in order to normalize evars on the fly. The basic primitive
to observe an `EConstr.t` is the following function:
```
val kind : Evd.evar_map -> t -> (t, t, ESorts.t, EInstance.t) Constr.kind_of_term
(** Same as {!Constr.kind} except that it expands evars and normalizes
    universes on the fly. *)
```

Essentially, each time it sees an evar which happens to be defined in the
provided evar-map, it replaces it with the corresponding body and carries on.

Due to universe unification occuring at the tactic level, the same goes for
universe instances and sorts. See the `ESort` and `EInstance` modules in
`EConstr`.

This normalization is critical for the soundness of tactics. Before EConstr, a
lot of bugs were lurking in the code base, a few still are (most notably in
meta-based unification) and failure to respect the guidelines thereafter may
result in nasal demons.

## Transition path

### Types

As a rule of thumb, all functions living at the tactic level should manipulate
`EConstr.t` instead of `Constr.t`, and similarly for the other data structures.

To ease the transition, the `EConstr` module defines a handful of aliases to
shadow the type names from the kernel.

It is recommended to perform the following replacement in headers.
```ocaml
(** Kernel types. You may remove the two following opens if you want. Beware
    that [kind_of_term] needs to be in scope if you use [EConstr.kind] so that
    you may still need to open one of the two. *)
open Term
open Constr
(** Tactic types. Open this after to shadow kernel types. *)
open EConstr
```

Note that the `EConstr` module also redefines a `Vars` submodule.

### Evar-map-passing

All functions deconstructing an econstr need to take an evar-map as a parameter.
Therefore, you need to pass one as an argument virtually everywhere.

In the Coq source code, it is recommended to take the evar-map as a first
argument called `sigma`, except if the function also takes an environment in
which case it is passed second. Namely, the two typical instances are:
```ocaml
let foo sigma c = mycode
val foo : Evd.evar_map -> EConstr.t -> Foo.t

let bar env sigma c = mycode
val bar : Environ.env -> Evd.evar_map -> EConstr.t -> Bar.t
```

The EConstr API makes the code much more sensitive to evar-maps, because a
lot of now useless normalizations were removed. Thus one should be cautious of
**not** dropping the evar-map when it has been updated, and should rather stick
to a strict state-passing discipline. Unsound primitives like
`Typing.unsafe_type_of` are also a known source of problems, so you should
replace them with the corresponding evar-map-returning function and thread it
properly.

### Functions

Many functions from `Constr` and `Term` are redefined to work on econstr in
the `EConstr` module, so that it is often enough to perform the `open` as
described above to replace them. Their type may differ though, because they now
need access to an evar-map. A lot of econstr-manipulating functions are also
defined in [`Termops`](/engine/termops.mli).

Functions manipulating tactic terms and kernel terms share the same name if they
are the equivalent one of the other. Do not hesitate to grep Coq mli files to
find the equivalent of a function you want to port if it is neither in `EConstr`
nor in `Termops` (this should be very rare).

### Conversion

Sometimes you do not have any other choice than calling kernel-side functions
on terms, and conversely to turn a kernel term into a tactic term.

There are two functions to do so.
* `EConstr.of_constr` turns kernel terms into tactic terms. It is currently
the physical identity, and thus O(1), but this may change in the future.
* `EConstr.to_constr` turns tactic terms into kernel terms. It performs a
full-blown normalization of the given term, which is O(n) and potentially
costly.

For performance reasons, avoiding to jump back and forth between kernel and
tactic terms is recommended.

There are also a few unsafe conversion functions that take advantage of the
fact that `EConstr.t` is internally the same as `Constr.t`. Namely,
`EConstr.Unsafe.to_constr` is the physical identity. It should **not** be used
in typical code and is instead provided for efficiency **when you know what you
are doing**. Either use it to reimplement low-level functions that happen to
be insensitive externally, or use it to provide backward compatibility with
broken code that relies on evar-sensitivity. **Do not use it because it is
easier than stuffing evar-maps everywhere.** You've been warned.

## Notes

The EConstr branch fixed a lot of eisenbugs linked to lack of normalization
everywhere, most notably in unification. It may also have introduced a few, so
if you see a change in behaviour *that looks like a bug*, please report it.
Obviously, unification is not specified, so it's hard to tell apart, but still.

Efficiency has been affected as well. We now pay an overhead when observing a
term, but at the same time a lot of costly upfront normalizations were removed.
