# Add sized typing to the kernel


<!-- Thank you for your contribution.
     Make sure you read the contributing guide and fill this template. -->


<!-- Keep what applies -->
**Kind:** feature.


<!-- If this is a bug fix, make sure the bug was reported beforehand. -->
Relevant discussion [here](https://github.com/coq/coq/wiki/CoqTerminationDiscussion#sized).


<!-- If there is a user-visible change in coqc/coqtop/coqchk/coq_makefile behavior and testing is not prohibitively expensive: -->
<!-- (Otherwise, remove this line.) -->
<!-- [ ] Added / updated test-suite -->
<!-- If this is a feature pull request / breaks compatibility: -->
<!-- (Otherwise, remove these lines.) -->
- [ ] Corresponding documentation was added / updated (including any warning and error messages added / removed / modified).
- [ ] Entry added in the changelog (see https://github.com/coq/coq/tree/master/doc/changelog#unreleased-changelog for details).


# Summary

The purpose of this draft pull request is a) to bring attention to the work that has been done with implementing sized types in Coq here, and b) to solicit help with development, debugging, design suggestions, etc.

This implements CIC^\*, a CIC with sized types, in the kernel's main type-checking algorithm by doing size inference on fully-elaborated terms; users do not (and cannot) provide size annotations themselves. It is based on Jorge Luis Sacchini's work on sized types in CIC (various papers), and the formal details of CIC^\* is provided in [Practical Sized Typing for Coq](https://arxiv.org/abs/1912.05601). See the Related Work section of PSTC for references to related languages such as CIC^\_, CIC^, and CC^\_\omega.

As opposed to sized types in Agda, sizes are not first-class, and do not appear in Gallina, only in the core language. The original philosophy behind this design is that existing code should not require any additional annotations to take advantage of type-based termination using sized types. All size annotations are inferred from the existing code, and termination- and productivity-checking is essentially constraint-checking relations between stage variables.

There exist terms which don't type-check in CIC^\* but do pass the existing guard check, and vice versa. `gcd` is an example of the former, and `quicksort` and example of the latter; these and more examples are provided in `README.v`. Therefore, we can take advantage of both methods of termination-checking (and checking productivity) by accepting terms that pass either sized typing or guard checking.

There are no metatheoretical results yet for CIC^\*. CIC^ and various other dialects of CIC with sized types have an array of metatheory (proofs of subject reduction, strong normalization, well-typedness of size inference, etc.). Work is currently undergoing in this area.

# Usage

Sized typing is off by default; turn it on with the flag `Set Sized Typing`. If both `Guard Checking` and `Sized Typing` are on, terms will pass type checking if *either* it passes the original guard check (`Inductive.check_fix`) *or* sized typing (`Stages.rec_check`).

# Technical Details

## Structure of stages and constraints

There's a giant comment in `Stages.mli` that will be informative.

## Very brief summary of the size inference algorithm

1. Every (co)inductive type is given a fresh stage variable. Constants, variables, and relatives are given a vector of fresh stage variables corresponding to how many stage variables the body they refer to needs.
2. During type checking, checking a subtyping relation (via `conv` functions) can generate substaging relations based on the subtyping rules. These form a set of substaging constraints.
3. At the end of type checking (co)fixpoints, we also check that the substaging constraints have no negative cycles, where substaging relations correspond to directed graph weights. If they do, then type checking fails.
4. Well-typed terms then have their annotations erased to \infty, except for position annotations, which mark where (co)recursive arguments occur.

## Differences between the implementation and PSTC

Features mostly orthogonal to sized typing are not mentioned in PSTC, including `SProp`, polymorphic universes, modules, and typeclasses.

PSTC describes an algorithm that guesses the recursive indices of fixpoints during size inference; in the implementation, this is (still) done during pretyping (via `Pretyping.search_guard`).

## Differences between PSTC and related work

CIC^ adds to inductive types a vector of polarities for each type parameter. We instead assume all type parameters are size-invariant and that all (co)inductive signatures, however they are currently checked, are all well-formed.

CIC^\_ disallows free stage variables in non-type locations within terms. This prevents us from defining type aliases (e.g. `Definition myNat := nat.`), so we have removed this restriction. We then add a vector of stage annotations to constants, variables, and relatives so that all (co)inductive types can properly be assigned stage annotations. This is probably similar to how polymorphic universes work.

We add a new kind of annotation, global position annotations, which mark the argument and return types of global definitions that have the "same" size.

## Overview of significant changes to OCaml codebase

As mentioned, `Constr.constr` variants `Ind`, `Rel`, `Var`, and `Const` have extra stage annotations, as well as `CClosure.fterm`'s variants `FFlex` and `FInd`.

`Constr.(l)eq_constr_univs`, used for subtyping comparisons between constructions, now returns a set of substaging constraints as well. Some `conv` functions (esp. in `Reduction`) also return a set of constraints.

A `check_sized` typing flag has been added to the environment, with the corresponding vernacular `Sized Typing` in `Vernacentries`. `Pretyping.search_guard` uses `Inductive.check_fix` and `Typeops.infer_fix` depending on sized typing and guard checking flags.

Everywhere where `search_guard` is called, a `Univ.ContextSet.t` is pushed into the environment.

Important new files include `Stages`, `Staging`, `WeightedDigraph`. Files that have been heavily modified are `Typeops`, `Constr`, `Inductive`, and `Reduction`. There are Coq tests in `sized_typing.v` and OCaml unit tests in `stages_tests.ml`.

The file `checker/values.ml` has been altered accordingly. I don't know what this does.

# Problems to Fix

* The following Coq code incorrectly fails to type check:

  ```coq
  Unset Guard Checking.
  Set Sized Typing.

  Definition outer :=
  let id x := x in
  fix f n :=
    match n with
    | O => O
    | S n' => f (id n')
    end.
  ```
  This is caused by the call to `Typeops.infer_fix` within `Pretyping.search_guard`. Inference is called on the fixpoint term `f`, while `id` lives in the environment. However, since size inference has not been run on `id`, it has the incorrect type. Running inference on all named and rel contexts will not work, since at the pretyping stage, they may contain `Evar`s and `Meta`s, which cannot be handled by `Typeops`. I suspect everything in the kernel's `Typeops.execute` will have to be replicated in pretyping's `Typing.execute` to correctly deal with this.

* Some files in the standard library compile very slowly, e.g. `Byte.v` and `Field_theory.v` (see [this](https://gitlab.com/ionathanch/coq/-/jobs/567110467) build). The extra checks for fixpoints in `Typeops.execute` could be what's causing this performance hit.

* There seem to be a lot of similarities between the implementation of polymorphic universes and sized types. Maybe the design of the sized types implementation should be modified to be more similar to polymorphic universes, and maybe even reuse parts of its implementation (e.g. `UGraph`, perhaps).

* Counting the number of stage annotations in definitions every time a const/var/rel is encountered is ineffecient. This information should be saved in the environment.

* `Nativeconv` and `Vconv`'s `conv_val` don't produce sets of stage constraints. Is this necessary? Is this a problem?

* The sized-typing–related error messages are *horrendous*, as well as how (and when) stage annotations are printed.

* Files to remove: `README.v`, `draft-pull-request.md`.
