Compilation of critical bugs in stable releases of Coq
======================================================

This file recollects knowledge about critical bugs found in Coq since version 8.0.

<!-- generate using dev/tools/markdown-toc -->

## Table of Contents

  - [Non fixed bugs](#non-fixed-bugs)
      - [buffer overflow on large records and closures (infinite loop with OCaml 5)](#buffer-overflow-on-large-records-and-closures-infinite-loop-with-ocaml-5)
      - [memory corruption by evaluating on ill-typed terms (obtained from unsafe tactics)](#memory-corruption-by-evaluating-on-ill-typed-terms-obtained-from-unsafe-tactics)
      - [coqchk checks too little about primitive declarations](#coqchk-checks-too-little-about-primitive-declarations)
      - [Print Assumptions + Parameter Inline fails to report some inconsistent flags](#print-assumptions-parameter-inline-fails-to-report-some-inconsistent-flags)
      - [Print Assumptions does not report Unset Universe Checking used during functor application](#print-assumptions-does-not-report-unset-universe-checking-used-during-functor-application)
  - [Fixed bugs](#fixed-bugs)
    - [Typing constructions](#typing-constructions)
      - [substitution missing in the body of a let](#substitution-missing-in-the-body-of-a-let)
      - [missing lift in checking guard](#missing-lift-in-checking-guard)
      - [de Bruijn indice bug in checking guard of nested cofixpoints](#de-bruijn-indice-bug-in-checking-guard-of-nested-cofixpoints)
      - [de Bruijn indice bug in computing allowed elimination principle](#de-bruijn-indice-bug-in-computing-allowed-elimination-principle)
      - [bug in Prop<=Set conversion which made Set identifiable with Prop, preventing a proof-irrelevant interpretation of Prop](#bug-in-propset-conversion-which-made-set-identifiable-with-prop-preventing-a-proof-irrelevant-interpretation-of-prop)
      - [incorrect abstraction of sort variables in relevance marks on opaque constants](#incorrect-abstraction-of-sort-variables-in-relevance-marks-on-opaque-constants)
      - [guard checker forgot to check non-structural arguments of fixpoint](#guard-checker-forgot-to-check-non-structural-arguments-of-fixpoint)
      - [guard checker incorrectly detects match on match as returning a subterm](#guard-checker-incorrectly-detects-match-on-match-as-returning-a-subterm)
      - [guard checker does incorrect reduction across inner fixpoint, accepting wrong fixpoints](#guard-checker-does-incorrect-reduction-across-inner-fixpoint-accepting-wrong-fixpoints)
      - [guard checker does not account for cross calls to compute uniform arguments of a nested mutual fixpoint](#guard-checker-does-not-account-for-cross-calls-to-compute-uniform-arguments-of-a-nested-mutual-fixpoint)
      - [guard checker does not check for correct recursive calls when passed as uniform argument in a nested fixpoint](#guard-checker-does-not-check-for-correct-recursive-calls-when-passed-as-uniform-argument-in-a-nested-fixpoint)
      - [guard checker does not count argument-less recursive calls to compute uniform arguments of a nested mutual fixpoint](#guard-checker-does-not-count-argument-less-recursive-calls-to-compute-uniform-arguments-of-a-nested-mutual-fixpoint)
      - [guard checker does not check arguments of recursive calls in uniformity analysis](#guard-checker-does-not-check-arguments-of-recursive-calls-in-uniformity-analysis)
      - [guard checker sometimes does reduction in the wrong context accepting wrong fixpoints](#guard-checker-sometimes-does-reduction-in-the-wrong-context-accepting-wrong-fixpoints)
      - [guard checker sometimes forgets to check lambda domains in nested fixpoints](#guard-checker-sometimes-forgets-to-check-lambda-domains-in-nested-fixpoints)
      - [cofixpoint guard checker passes wrong rectree for nested mutual cofixpoints](#cofixpoint-guard-checker-passes-wrong-rectree-for-nested-mutual-cofixpoints)
      - [guard checker counts local definitions as formal arguments in uniformity analysis](#guard-checker-counts-local-definitions-as-formal-arguments-in-uniformity-analysis)
    - [Module system](#module-system)
      - [missing universe constraints in typing "with" clause of a module type](#missing-universe-constraints-in-typing-with-clause-of-a-module-type)
      - [universe constraints for module subtyping not stored in vo files](#universe-constraints-for-module-subtyping-not-stored-in-vo-files)
      - [module subtyping disrespected squashing status of inductives](#module-subtyping-disrespected-squashing-status-of-inductives)
      - [Functor inlining drops universe substitution](#functor-inlining-drops-universe-substitution)
      - [Primitives are incorrectly considered convertible to anything by module subtyping](#primitives-are-incorrectly-considered-convertible-to-anything-by-module-subtyping)
      - [Missing substitution when strengthening functors](#missing-substitution-when-strengthening-functors)
      - [Missing substitution when strengthening aliased functors](#missing-substitution-when-strengthening-aliased-functors)
      - [Incorrect subtyping rule for universe polymorphic "with Definition".](#incorrect-subtyping-rule-for-universe-polymorphic-with-definition)
      - [Subtyping ignored elimination constraints](#subtyping-ignored-elimination-constraints)
      - [kernel and checker accept incorrect name aliasing information](#kernel-and-checker-accept-incorrect-name-aliasing-information)
    - [Universes](#universes)
      - [issue with two parameters in the same universe level](#issue-with-two-parameters-in-the-same-universe-level)
      - [universe polymorphism can capture global universes](#universe-polymorphism-can-capture-global-universes)
      - [template polymorphism not collecting side constraints on the universe level of a parameter](#template-polymorphism-not-collecting-side-constraints-on-the-universe-level-of-a-parameter)
      - [more template polymorphism missing constraints](#more-template-polymorphism-missing-constraints)
      - [universe constraints erroneously discarded when forcing an asynchronous proof containing delayed monomorphic constraints inside a universe polymorphic section](#universe-constraints-erroneously-discarded-when-forcing-an-asynchronous-proof-containing-delayed-monomorphic-constraints-inside-a-universe-polymorphic-section)
      - [Set+2 incorrectly simplified to Set+1](#set2-incorrectly-simplified-to-set1)
      - [variance inference for section universes ignored use of section universes in inductives and axioms defined before the inductive being inferred](#variance-inference-for-section-universes-ignored-use-of-section-universes-in-inductives-and-axioms-defined-before-the-inductive-being-inferred)
      - [Missing substitution for relevance of product domain in lazy](#missing-substitution-for-relevance-of-product-domain-in-lazy)
      - [Missing stack conversion for irrelevant-to-relevant match](#missing-stack-conversion-for-irrelevant-to-relevant-match)
      - [Incorrect discharge of sort polymorphic inductive squashing with section polymorphic sort](#incorrect-discharge-of-sort-polymorphic-inductive-squashing-with-section-polymorphic-sort)
      - [Missing universe substitution in primitive array instance in lazy](#missing-universe-substitution-in-primitive-array-instance-in-lazy)
      - [Double universe substitution in letins from indices in match return clause](#double-universe-substitution-in-letins-from-indices-in-match-return-clause)
      - [Double universe substitution in letins from constructor arguments in match branches](#double-universe-substitution-in-letins-from-constructor-arguments-in-match-branches)
    - [Primitive projections](#primitive-projections)
      - [check of guardedness of extra arguments of primitive projections missing](#check-of-guardedness-of-extra-arguments-of-primitive-projections-missing)
      - [records based on primitive projections became possibly recursive without the guard condition being updated](#records-based-on-primitive-projections-became-possibly-recursive-without-the-guard-condition-being-updated)
      - [incorrect checking of subtyping with algebraic universes](#incorrect-checking-of-subtyping-with-algebraic-universes)
    - [Conversion machines](#conversion-machines)
      - [the invariant justifying some optimization was wrong for some combination of sharing side effects](#the-invariant-justifying-some-optimization-was-wrong-for-some-combination-of-sharing-side-effects)
      - [collision between constructors when more than 256 constructors in a type](#collision-between-constructors-when-more-than-256-constructors-in-a-type)
      - [wrong universe constraints](#wrong-universe-constraints)
      - [missing pops in executing 31bit arithmetic](#missing-pops-in-executing-31bit-arithmetic)
      - [primitive integer emulation layer on 32 bits not robust to garbage collection](#primitive-integer-emulation-layer-on-32-bits-not-robust-to-garbage-collection)
      - [broken long multiplication primitive integer emulation layer on 32 bits](#broken-long-multiplication-primitive-integer-emulation-layer-on-32-bits)
      - [broken addmuldiv operation for large shifts](#broken-addmuldiv-operation-for-large-shifts)
      - [translation of identifier from Coq to OCaml was not bijective, leading to identify True and False](#translation-of-identifier-from-coq-to-ocaml-was-not-bijective-leading-to-identify-true-and-false)
      - [stuck primitive projections computed incorrectly by native_compute](#stuck-primitive-projections-computed-incorrectly-by-native_compute)
      - [incorrect De Bruijn handling when inferring the relevance mark for a lambda](#incorrect-de-bruijn-handling-when-inferring-the-relevance-mark-for-a-lambda)
      - [buffer overflow on large accumulators](#buffer-overflow-on-large-accumulators)
      - [buffer overflow, arbitrary code execution on floating-point operations](#buffer-overflow-arbitrary-code-execution-on-floating-point-operations)
      - [arbitrary code execution on irreducible PArray.set](#arbitrary-code-execution-on-irreducible-parrayset)
      - [arbitrary code execution on arrays of floating point numbers](#arbitrary-code-execution-on-arrays-of-floating-point-numbers)
      - [conversion of Prod / Prod values was comparing the wrong components](#conversion-of-prod-prod-values-was-comparing-the-wrong-components)
      - [η-expansion of cofixpoints was performed in the wrong environment](#-expansion-of-cofixpoints-was-performed-in-the-wrong-environment)
      - [conversion would compare the mutated version of primitive arrays instead of undoing mutation where needed](#conversion-would-compare-the-mutated-version-of-primitive-arrays-instead-of-undoing-mutation-where-needed)
      - [tactic code could mutate a global cache of values for section variables](#tactic-code-could-mutate-a-global-cache-of-values-for-section-variables)
      - [incorrect handling of universe polymorphism](#incorrect-handling-of-universe-polymorphism)
      - [Forgotten universe substitution with Register Inline on universe polymorphic definition](#forgotten-universe-substitution-with-register-inline-on-universe-polymorphic-definition)
      - [conversion under contexts is done in the wrong environment](#conversion-under-contexts-is-done-in-the-wrong-environment)
    - [Side-effects](#side-effects)
      - [polymorphic side-effects inside monomorphic definitions incorrectly handled as not inlined](#polymorphic-side-effects-inside-monomorphic-definitions-incorrectly-handled-as-not-inlined)
      - [Section variables used in side effects not checked by Proof using](#section-variables-used-in-side-effects-not-checked-by-proof-using)
    - [Forgetting unsafe flags](#forgetting-unsafe-flags)
      - [unsafe typing flags used inside a section would not be reported by Print Assumptions after closing the section](#unsafe-typing-flags-used-inside-a-section-would-not-be-reported-by-print-assumptions-after-closing-the-section)
    - [Conflicts with axioms in library](#conflicts-with-axioms-in-library)
      - [axiom of description and decidability of equality on real numbers in library Reals was inconsistent with impredicative Set](#axiom-of-description-and-decidability-of-equality-on-real-numbers-in-library-reals-was-inconsistent-with-impredicative-set)
      - [guard condition was unknown to be inconsistent with propositional extensionality in library Sets](#guard-condition-was-unknown-to-be-inconsistent-with-propositional-extensionality-in-library-sets)
      - [incompatibility axiom of choice and excluded-middle with elimination of large singletons to Set](#incompatibility-axiom-of-choice-and-excluded-middle-with-elimination-of-large-singletons-to-set)
      - [Incorrect specification of PrimFloat.leb](#incorrect-specification-of-primfloatleb)
      - [Incorrect implementation of SFclassify.](#incorrect-implementation-of-sfclassify)
      - [nativenorm reading back closures as arbitrary floating-point values](#nativenorm-reading-back-closures-as-arbitrary-floating-point-values)
      - [guard condition issue made it inconsistent with propositional extensionality in library Sets](#guard-condition-issue-made-it-inconsistent-with-propositional-extensionality-in-library-sets)
    - [Deserialization](#deserialization)
      - [deserialization of .vo data not properly checked](#deserialization-of-vo-data-not-properly-checked)
  - [Probably non exploitable fixed bugs](#probably-non-exploitable-fixed-bugs)
      - [bug in 31bit arithmetic](#bug-in-31bit-arithmetic)

## Non fixed bugs

#### buffer overflow on large records and closures (infinite loop with OCaml 5)

- component: VM reduction machine
- introduced: 8.1
- impacted versions: 8.1-NOW
- impacted coqchk versions: none (no VM in coqchk)
- fixed in: NONE
- found by: Dolan, Roux, Melquiond
- GH issue number: ocaml/ocaml#6385, rocq-prover/rocq#13439
- exploit: ??
- risk: requires very large number of arguments, fix block size or nested letins

#### memory corruption by evaluating on ill-typed terms (obtained from unsafe tactics)

- component: VM and native reduction machines
- introduced: 8.1
- impacted versions: 8.1-NOW
- impacted coqchk versions: none (no VM or native in coqchk)
- fixed in: NONE
- found by: Gaëtan Gilbert, Andres Erbsen
- GH issue number: rocq-prover/rocq#16891
- exploit: requires a memory corruption to craft something that doesn't just SIGSEV
- risk: could be activated by chance but unlikely to produce anything
        other than SIGSEV outside a deliberate attack

#### coqchk checks too little about primitive declarations

- component: primitive types and operators
- introduced: v8.10 (#6914 primitive integers)
- impacted versions: coqchk only
- impacted coqchk versions: V8.10-NOW
- fixed in: NONE
- found by: Gaëtan Gilbert
- GH issue number: rocq-prover/rocq#12439
- exploit: not fully worked out, requires crafted .vo file
- risk: none (requires crafted .vo file)

#### Print Assumptions + Parameter Inline fails to report some inconsistent flags

- component: module functors
- introduced: rocq-prover/rocq#79
- impacted versions: V8.6-NOW
- impacted coqchk versions: none
- found by: Jason Gross
- GH issue number: rocq-prover/rocq#12155
- exploit: see issue
- risk: moderate if not using coqchk, none if using coqchk (coqchk rejects the produced file)

#### Print Assumptions does not report Unset Universe Checking used during functor application

- component: module functors
- introduced: v8.11 (#10291) or earlier
- impacted versions: V8.11-NOW
- impacted coqchk versions: none
- found by: Gaëtan Gilbert
- GH issue number: rocq-prover/rocq#16646
- exploit: see issue
- risk: moderate if not using coqchk, none if using coqchk (coqchk rejects the produced file)

## Fixed bugs

### Typing constructions

#### substitution missing in the body of a let

- component: "match"
- introduced: ?
- impacted released versions: V8.3-V8.3pl2, V8.4-V8.4pl4
- impacted development branches: none
- impacted coqchk versions: ?
- fixed in: master/trunk/v8.5 ([e583a79b5](https://github.com/rocq-prover/rocq/commit/e583a79b5a0298fd08f34305cc876d5117913e95), 22 Nov 2015, Herbelin), v8.4 ([525056f1](https://github.com/rocq-prover/rocq/commit/525056f1a630426b78668ab583e228c25b492c35), 22 Nov 2015, Herbelin), v8.3 ([4bed0289](https://github.com/rocq-prover/rocq/commit/4bed0289d66e6e413ccdea7a33dc747c83bce92e), 22 Nov 2015, Herbelin)
- found by: Herbelin
- exploit: test-suite/success/Case22.v
- GH issue number: ?
- risk: ?

#### missing lift in checking guard

- component: fixpoint, guard
- introduced: probably from V5.10
- impacted released versions: probably V5-V7, V8.0-V8.0pl4, V8.1-V8.1pl4
- impacted development branches: v8.0 ?
- impacted coqchk versions: ?
- fixed in: master/trunk/v8.2 ([ff45afa8](https://github.com/rocq-prover/rocq/commit/ff45afa83a9235cbe33af525b6b0c7985dc7e091), r11646, 2 Dec 2008, Barras), v8.1 ([f8e7f273](https://github.com/rocq-prover/rocq/commit/f8e7f273f2e6009c3c0f0eee47c33542a6fdf361), r11648, 2 Dec 2008, Barras)
- found by: Barras
- exploit: test-suite/failure/guard.v
- GH issue number: none
- risk: unprobable by chance

#### de Bruijn indice bug in checking guard of nested cofixpoints

- component: cofixpoint, guard
- introduced: after V6.3.1, before V7.0
- impacted released versions: V8.0-V8.0pl4, V8.1-V8.1pl4, V8.2-V8.2pl2, V8.3-V8.3pl2, V8.4-V8.4pl4
- impacted development branches: none
- impacted coqchk versions: ?
- fixed in: master ([9f81e2c36](https://github.com/rocq-prover/rocq/commit/9f81e2c360c2be764e71d21ed7c266ee6e8a88c5), 10 Apr 2014, Dénès), v8.4 ([f50ec9e7d](https://github.com/rocq-prover/rocq/commit/f50ec9e7dbd082c9a465aedda25427d93e12cabe), 11 Apr 2014, Dénès), v8.3 ([40c0fe7f4](https://github.com/rocq-prover/rocq/commit/40c0fe7f44b3c99bec5188e01197c8a77348a4ee), 11 Apr 2014, Dénès), v8.2 ([06d66df8c](https://github.com/rocq-prover/rocq/commit/06d66df8c713307625b1c40c054ca06c00ff74b3), 11 Apr 2014, Dénès), v8.1 ([977afae90](https://github.com/rocq-prover/rocq/commit/977afae90c4e2aa974232b0c664346db72aadaa3), 11 Apr 2014, Dénès), v8.0 ([f1d632992](https://github.com/rocq-prover/rocq/commit/f1d632992e33a74b30e79271bd3748d69c5a2152), 29 Nov 2015, Herbelin, backport)
- found by: Dénès
- exploit: ?
- GH issue number: none ?
- risk: ?

#### de Bruijn indice bug in computing allowed elimination principle

- component: inductive types, elimination principle
- introduced: 23 May 2006, [9c2d70b](https://github.com/rocq-prover/rocq/commit/9c2d70b91341552e964979ba09d5823cc023a31c), r8845, Herbelin (part of template polymorphism)
- impacted released versions: V8.1-V8.1pl4, V8.2-V8.2pl2, V8.3-V8.3pl2, V8.4-V8.4pl4
- impacted development branches: none
- impacted coqchk versions: ?
- fixed in: master ([8a01c3685](https://github.com/rocq-prover/rocq/commit/8a01c36850353c1875383cbc788cec9c42590b57), 24 Jan 2014, Dénès), v8.4 ([8a01c3685](https://github.com/rocq-prover/rocq/commit/8a01c36850353c1875383cbc788cec9c42590b57), 25 Feb 2014, Dénès), v8.3 ([2b3cc4f85](https://github.com/rocq-prover/rocq/commit/2b3cc4f85cc134fe58c21d720851e275e6a77ea0), 25 Feb 2014, Dénès), v8.2 ([459888488](https://github.com/rocq-prover/rocq/commit/4598884884d6db00c485189e3a3b793b05814928), 25 Feb 2014, Dénès), v8.1 ([79aa20872](https://github.com/rocq-prover/rocq/commit/79aa208728420747a933f38b3aa101c92f4dcde0), 25 Feb 2014, Dénès)
- found by: Dénès
- exploit: see rocq-prover/rocq#3211
- GH issue number: rocq-prover/rocq#3211
- risk: ?

#### bug in Prop<=Set conversion which made Set identifiable with Prop, preventing a proof-irrelevant interpretation of Prop

- component: universe subtyping
- introduced: V8.2 ([bba897d5f](https://github.com/rocq-prover/rocq/commit/bba897d5fd964bef0aa10102ef41cee1ac5fc3bb), 12 May 2008, Herbelin)
- impacted released versions: V8.2-V8.2pl2
- impacted development branches: none
- impacted coqchk versions: ?
- fixed in: master/trunk ([679801](https://github.com/rocq-prover/rocq/commit/679801623c1f55d0081f952c2094c3572fa39d4f), r13450, 23 Sep 2010, Glondu), v8.3 ([309a53f2](https://github.com/rocq-prover/rocq/commit/309a53f2e1aa9b2a39654cf5fa23eb632a04c22f), r13449, 22 Sep 2010, Glondu), v8.2 (41ea5f08, r14263, 6 Jul 2011, Herbelin, backport)
- found by: Georgi Guninski
- exploit: test-suite/failure/prop_set_proof_irrelevance.v
- GH issue number: none?
- risk: ?

#### incorrect abstraction of sort variables in relevance marks on opaque constants

and lack of checking of relevance marks on constants in coqchk

- component: sort polymorphism / proof irrelevance
- introduced: V8.10 for the coqchk bug, V8.19 for the coqc bug
- impacted released versions: V8.19.0
- impacted coqchk: versions: V8.10-V8.19.0
- fixed in: V8.19.1, V8.20
- found by: Gaëtan Gilbert
- exploit / GH issue: [#18629](https://github.com/rocq-prover/rocq/issues/18629)
- risk: low (requires specific plugin code unlikely to be found in non malicious plugin)

#### guard checker forgot to check non-structural arguments of fixpoint

- component: guard checking
- introduced: V8.16 ([#15434](https://github.com/rocq-prover/rocq/pull/15434))
- impacted released versions: V8.16 to V9.0.0
- impacted coqchk versions: Same
- fixed in: V9.0.1, V9.1.0
- found by: ccz181078
- exploit / GH issue: [#20413](https://github.com/rocq-prover/rocq/issues/20413)
- risk: significant (bad terms may be generated by Program machinery)

#### guard checker incorrectly detects match on match as returning a subterm

- component: guard checking
- introduced: V8.16 ([#15434](https://github.com/rocq-prover/rocq/pull/15434))
- impacted released versions: V8.16 to V9.0.0
- impacted coqchk versions: Same
- fixed in: V9.0.1, V9.1.0
- found by: Yann Leray
- exploit / GH issue: [#20455](https://github.com/rocq-prover/rocq/issues/20455)
- risk: unknown (no development in CI was affected)

#### guard checker does incorrect reduction across inner fixpoint, accepting wrong fixpoints

- component: guard checking
- introduced: V8.16 ([#15434](https://github.com/rocq-prover/rocq/pull/15434))
- impacted released versions: V8.16 to V9.0.0
- impacted coqchk versions: Same
- fixed in: V9.0.1, V9.1.0 ([#20648](https://github.com/rocq-prover/rocq/issues/20648))
- found by: Yann Leray
- exploit / GH issue: [#20555](https://github.com/rocq-prover/rocq/issues/20555)
- risk: unknown (no development in CI was affected)

#### guard checker does not account for cross calls to compute uniform arguments of a nested mutual fixpoint
- component: guard checking
- introduced: V8.20 ([#17986](https://github.com/rocq-prover/rocq/pull/17986))
- impacted released versions: V8.20, V9.0, V9.1
- impacted coqchk versions: Same
- fixed in: V9.2.0 ([#21684](https://github.com/rocq-prover/rocq/pull/21684))
- found by: Tristan Stérin
- exploit / GH issue: [#21682](https://github.com/rocq-prover/rocq/issues/21682)
- risk: unknown (no development in CI was affected)

#### guard checker does not check for correct recursive calls when passed as uniform argument in a nested fixpoint
- component: guard checking
- introduced: V9.0.1, V9.1.0 ([#20648](https://github.com/rocq-prover/rocq/issues/20648), see 2 above)
- impacted released versions: V9.0.1, V9.1.0, V9.1.1
- impacted coqchk versions: Same
- fixed in: V9.2.0 ([#21684](https://github.com/rocq-prover/rocq/pull/21684))
- found by: Tristan Stérin
- exploit / GH issue: [#21683](https://github.com/rocq-prover/rocq/issues/21683)
- risk: unknown (no development in CI was affected)

#### guard checker does not count argument-less recursive calls to compute uniform arguments of a nested mutual fixpoint
- component: guard checking
- introduced: V8.20 ([#17986](https://github.com/rocq-prover/rocq/pull/17986))
- impacted released versions: V8.20, V9.0, V9.1
- impacted coqchk versions: Same
- fixed in: V9.2.0 ([#21684](https://github.com/rocq-prover/rocq/pull/21684))
- found by: Tristan Stérin
- exploit / GH issue: [#21701](https://github.com/rocq-prover/rocq/issues/21701)
- risk: unknown (no development in CI was affected)

#### guard checker does not check arguments of recursive calls in uniformity analysis
- component: guard checking
- introduced: V8.20 ([#17986](https://github.com/rocq-prover/rocq/pull/17986))
- impacted released versions: V8.20, V9.0, V9.1
- impacted coqchk versions: Same
- fixed in: V9.2.0 ([#21798](https://github.com/rocq-prover/rocq/pull/21798))
- found by: Pierre-Marie Pédrot
- exploit / GH issue: [#21797](https://github.com/rocq-prover/rocq/issues/21797)
- risk: unknown (no development in CI was affected)

#### guard checker sometimes does reduction in the wrong context accepting wrong fixpoints
- component: guard checking
- introduced: V8.16 ([#15453](https://github.com/rocq-prover/rocq/pull/15453))
- impacted released versions: V8.16, V8.17, V8.19, V8.20, V9.0, V9.1, V9.2.0
- impacted coqchk versions: Same
- fixed in: V9.3 ([#21845](https://github.com/rocq-prover/rocq/pull/21845))
- found by: Yann Leray
- exploit / GH issue: [#21839](https://github.com/rocq-prover/rocq/issues/21839)
- risk: unknown (no development in CI was affected)

#### guard checker sometimes forgets to check lambda domains in nested fixpoints
- component: guard checking
- introduced: V8.20 ([#17986](https://github.com/rocq-prover/rocq/pull/17986))
- impacted released versions: V8.20, V9.0, V9.1, V9.2.0
- impacted coqchk versions: Same
- fixed in: V9.2.1, V9.3 ([#22022](https://github.com/rocq-prover/rocq/pull/22022))
- found by: Yann Leray
- exploit / GH issue: [#22021](https://github.com/rocq-prover/rocq/issues/22021)
- risk: low (no known way to exploit the issue)

#### incorrect reification in lazy machine of matches with universe polymorphism
- component: "lazy" reduction
- introduced: V8.17
- impacted released versions: V8.17 to V9.2.0
- impacted rocqchk versions: same
- fixed in: V9.2.1, V9.3
- found by: OpenAI
- issue: #22380
- risk: reification of the lazy machine is only trusted
  when it is used to check an application or match/proj
  (typically in `f x`, the inferred type of `f` is reduced to expose a `forall`).
  The bug occurs when the reduced type has a stuck match on a universe polymorphic inductive.
  The exploit in the issue uses Definitional UIP but the code is incorrect even without that flag.

#### variance inference ignores stack of stuck irrelevant to relevant matches
- component: inductive declarations, universe polymorphism
- introduced: 8.13
- impacted released versions: V8.13 to V9.2.0
- impacted rocqchk versions: same
- fixed in: V9.2.1, V9.3
- found by: OpenAI
- issue: #22376
- risk: needs a cumulative inductive in which a match on an empty SProp inductive
  or inductive using Definitional UIP appears

#### missing universe substitution when converting matches with letin in constructor type
- component: conversion
- introduced: V8.17
- impacted released versions: V8.17 to V9.2.0
- impacted rocqchk versions: same
- fixed in: V9.2.1, V9.3
- found by: OpenAI
- issue: #22391
- risk: needs to convert stuck matches of a universe polymorphic inductive
  with a letin in the constructor type. The bug only appears if a polymorphic universe is used in the letin's body, and the match uses the letin.

#### incorrect variance inference with letin in constructor type
- component: inductive declarations, universe polymorphism
- introduced: V8.6 (cumulative inductives)
- impacted released versions: V8.6 to V9.2.0
- impacted rocqchk versions: same
- fixed in: V9.2.1, V9.3
- found by: OpenAI
- issue: #22385
- risk: the bug comes from being able to bind a constructor type letin in a match,
  which means those letins cannot be irrelevant for conversion.
  Differences in reduction may mean the bug is harder to exploit before V8.19, see issue.

#### cofixpoint guard checker passes wrong rectree for nested mutual cofixpoints
- component: cofixpoints, guard checking
- introduced: before V7.0, probably when coinductives first appeared
- impacted released versions: all releases until V9.2.0 included
- impacted coqchk versions: Same
- fixed in: V9.2.1, V9.3 ([#22392](https://github.com/rocq-prover/rocq/pull/22392))
- found by: Daniel Selsam
- exploit / GH issue: [#22389](https://github.com/rocq-prover/rocq/issues/22389)
- risk: ?

#### cofixpoint guard checker computes rectree in the wrong environment
- component: cofixpoints, guard checking
- introduced: before V7.0, probably when coinductives first appeared
- impacted released versions: all releases until V9.2.0 included
- impacted coqchk versions: Same
- fixed in: V9.2.1, V9.3 ([#22388](https://github.com/rocq-prover/rocq/pull/22388))
- found by: Daniel Selsam
- exploit / GH issue: [#22386](https://github.com/rocq-prover/rocq/issues/22386)
- risk: ?

#### guard checker counts local definitions as formal arguments in uniformity analysis
- component: guard checking
- introduced: V8.20 ([#17986](https://github.com/rocq-prover/rocq/pull/17986))
- impacted released versions: V8.20, V9.0, V9.1, V9.2.0
- impacted coqchk versions: Same
- fixed in: V9.2.1, V9.3 ([#22384](https://github.com/rocq-prover/rocq/pull/22384))
- found by: Daniel Selsam
- exploit / GH issue: [#22382](https://github.com/rocq-prover/rocq/issues/22382)
- risk: ?


### Module system

#### missing universe constraints in typing "with" clause of a module type

- component: modules, universes
- introduced: ?
- impacted released versions: V8.3-V8.3pl2, V8.4-V8.4pl6; unclear for V8.2 and previous versions
- impacted development branches: none
- impacted coqchk versions: ?
- fixed in: master/trunk ([d4869e059](https://github.com/rocq-prover/rocq/commit/d4869e059bfb73d99e1f5ef1b0a1f0906fa27056), 2 Oct 2015, Sozeau), v8.4 ([40350ef3b](https://github.com/rocq-prover/rocq/commit/40350ef3b34b0be9d5ceddde772218c2f2dafe32), 9 Sep 2015, Sozeau)
- found by: Dénès
- exploit: test-suite/bugs/bug_4294.v
- GH issue number: rocq-prover/rocq#4294
- risk: ?

#### universe constraints for module subtyping not stored in vo files

- component: modules, universes
- introduced: presumably 8.2 ([b3d3b56](https://github.com/rocq-prover/rocq/commit/b3d3b566c5b5f34ab518c587f62530abde131be8))
- impacted released versions: 8.2, 8.3, 8.4
- impacted development branches: v8.5
- impacted coqchk versions: none
- fixed in: v8.2 ([c1d9889](https://github.com/rocq-prover/rocq/commit/c1d988904483eb1f3a8917ea08fced1240e3844b)), v8.3 (8056d02), v8.4 ([a07deb4](https://github.com/rocq-prover/rocq/commit/a07deb4eac1d5f886159784ef5d8d006892be547)), trunk ([0cd0a3e](https://github.com/rocq-prover/rocq/commit/0cd0a3ecdc7f942da153c59369ca3572bd18dd10)) Mar 5, 2014, Tassi
- found by: Tassi by running coqchk on the mathematical components library
- exploit: requires multiple files, no test provided
- GH issue number: rocq-prover/rocq#3243
- risk: could be exploited by mistake

#### module subtyping disrespected squashing status of inductives

- component: modules, universes, inductives
- introduced: probably 7.4 ([1296520](https://github.com/rocq-prover/rocq/commit/12965209478bd99dfbe57f07d5b525e51b903f22))
- impacted released versions: until 8.15.0
- impacted coqchk versions: none
- fixed in: 8.15.1, 8.16
- found by: Pédrot
- exploit: see GitHub issue
- GH issue number: rocq-prover/rocq#15838
- risk: unlikely (caught by coqchk, needs Unset Elimination Schemes in the module type)

#### Functor inlining drops universe substitution

- component: Modules
- introduced: ?
- impacted released versions: ??-V8.8.0
- impacted coqchk versions: same? not sure if coqchk has a this bug
- fixed in: V8.8.1, V8.9.0 (#7616)
- found by: Pierre-Marie Pédrot
- GH issue number: rocq-prover/rocq#7615
- exploit: see issue
- risk: medium

#### Primitives are incorrectly considered convertible to anything by module subtyping

- component: modules, primitive types
- introduced: 8.11
- impacted released versions: V8.11.0-V8.18.0
- impacted coqchk versions: same
- fixed in: V8.19.0
- found by: Gaëtan Gilbert
- GH issue number: rocq-prover/rocq#18503
- exploit: see issue
- risk: high if there is a Primitive in a Module Type, otherwise low

#### Missing substitution when strengthening functors

- component: modules
- introduced: 8.5 for the kernel (c5b699f), 8.10 for the checker (#8773)
- impacted released versions: 8.5-9.0.0
- impacted coqchk version: 8.10-9.0.0
- fixed in: V9.0.1
- found by: Pierre-Marie Pédrot
- GH issue number: rocq-prover/rocq#21051
- exploit: see issue
- risk: could be exploited by mistake when using heavy module machinery

#### Missing substitution when strengthening aliased functors

- component: modules
- introduced: 8.5 for the kernel (c5b699f), 8.10 for the checker (#8773)
- impacted released versions: 8.5-9.1
- impacted coqchk version: 8.10-9.1
- fixed in: V9.2.0
- found by: Tristan Stérin
- GH issue number: rocq-prover/rocq#21685
- exploit: see issue
- risk: could be exploited by mistake when using heavy module machinery

#### Incorrect subtyping rule for universe polymorphic "with Definition".

- component: modules
- introduced: 8.5
- impacted released versions: 8.5-9.1
- impacted coqchk version: none
- fixed in: V9.2.0
- found by: Tristan Stérin
- GH issue number: rocq-prover/rocq#21702
- exploit: see issue
- risk: moderate, requires uncommon features

#### Subtyping ignored elimination constraints

- component: modules, sort polymorphism
- introduced: V9.2+rc1
- impacted released versions: none
- impacted coqchk versions: none
- fixed in: V9.2.0
- found by: Yann Leray
- GH issue number: rocq-prover/rocq#21750
- exploit: see issue
- risk: high when combining module subyping with sort polymorphism
  (but not possible in non-rc version)

#### kernel and checker accept incorrect name aliasing information

- component: name handling / typechecker
- introduced: a long time ago
- impacted versions: until 9.2.0
- impacted coqchk versions: same
- fixed in: 9.2.0
- found by: Pierre-Marie Pédrot
- GH issue number: rocq-prover/rocq#7609
- exploit: see issue (requires a plugin or hand crafted .vo file)
- risk: low

### Incorrect subtyping of inductives with letins in constructor types
- component: subtyping, inductive declarations
- introduced: unclear, possibly only exploitable since V8.14 (#13563)
- impacted versions: until V9.2.0
- fixed in: 9.2.0, 9.3
- found by: OpenAI
- issue: #22387
- risk: need to use module subtyping to confuse inductives with different letins,
  and use those letins in a match.

### Including functor application generates garbage delta-resolvers

- component: module inclusion and functors
- introduced: unclear, only exploitable since #21905
- impacted released versions: V9.3+rc1
- fixed in: 9.2.1, 9.3.0
- found by: Pierre-Marie Pédrot flanked by Claude Opus 5
- issue: #22409
- risk: any development relying on inclusion of functor applications

### Universes

#### issue with two parameters in the same universe level

- component: template polymorphism
- introduced: 23 May 2006, [9c2d70b](https://github.com/rocq-prover/rocq/commit/9c2d70b91341552e964979ba09d5823cc023a31c), r8845, Herbelin
- impacted released versions: V8.1-V8.1pl4, V8.2-V8.2pl2, V8.3-V8.3pl2
- impacted development branches: none
- impacted coqchk versions: ?
- fixed in: trunk/master/v8.4 ([8082d1faf](https://github.com/rocq-prover/rocq/commit/8082d1faf85a0ab29f6c144a137791902a4e9c1f), 5 Oct 2011, Herbelin), V8.3pl3 ([bb582bca2](https://github.com/rocq-prover/rocq/commit/bb582bca2ca3fd94df01aad8d8070f8d129b25b3), 5 Oct 2011, Herbelin), v8.2 branch ([3333e8d3](https://github.com/rocq-prover/rocq/commit/3333e8d3387b3bc4d3ceb75aad853f8e455af444), 5 Oct 2011, Herbelin), v8.1 branch ([a8fc2027](https://github.com/rocq-prover/rocq/commit/a8fc2027258e1fb2defd05344e1249374f6e4e19), 5 Oct 2011, Herbelin),
- found by: Barras
- exploit: test-suite/failure/inductive.v
- GH issue number: none
- risk: unlikely to be activated by chance

#### universe polymorphism can capture global universes

- component: universe polymorphism
- impacted released versions: V8.5 to V8.8
- impacted coqchk versions: V8.5 to V8.9
- fixed in: [ec4aa4971f](https://github.com/rocq-prover/rocq/commit/ec4aa4971f7789eeccec2f38f2bb7ec976f87ede) ([58e1d0f200](https://github.com/rocq-prover/rocq/commit/58e1d0f2006f3243cbf7b57a9858f5119ffea666) for the checker)
- found by: Gaëtan Gilbert
- exploit: test-suite/misc/poly-capture-global-univs
- GH issue number: rocq-prover/rocq#8341
- risk: unlikely to be activated by chance (requires a plugin)

#### template polymorphism not collecting side constraints on the universe level of a parameter

this is a general form of the previous issue about template
polymorphism exploiting other ways to generate untracked constraints

- component: template polymorphism
- introduced: morally at the introduction of template polymorphism, 23
- May 2006, [9c2d70b](https://github.com/rocq-prover/rocq/commit/9c2d70b91341552e964979ba09d5823cc023a31c), r8845, Herbelin
- impacted released versions: at least V8.4-V8.4pl6, V8.5-V8.5pl3,
  V8.6-V8.6pl2, V8.7.0-V8.7.1, V8.8.0-V8.8.1, V8.9.0-V8.9.1, in theory
  also V8.1-V8.1pl4, V8.2-V8.2pl2, V8.3-V8.3pl2 but not exploit found
  there yet (an exploit using a plugin to force sharing of universe
  level is in principle possible though)
- impacted development branches: all from 8.4 to 8.9 at the time of writing and suspectingly also all from 8.1 to 8.4 if a way to create untracked constraints can be found
- impacted coqchk versions: a priori all (tested with V8.4 and V8.9 which accept the exploit)
- fixed in: V8.10.0 ([eb3f8225a2](https://github.com/rocq-prover/rocq/commit/eb3f8225a286aef3a57ad876584b4a927241ff69), PR rocq-prover/rocq#9918, Aug 2019, Dénès and Sozeau)
- found by: Gilbert using explicit sharing of universes, exploit found for 8.5-8.9 by Pédrot, other variants generating sharing using sections, or using ltac tricks by Sozeau, exploit in 8.4 by Herbelin and Jason Gross by adding new tricks to Sozeau's variants
- exploit: test-suite/failure/Template.v
- GH issue number: rocq-prover/rocq#9294
- risk: moderate risk to be activated by chance

#### more template polymorphism missing constraints

using the same universe in the parameters and the constructor
arguments of a template polymorphic inductive (using named universes
in modern Coq, or unification tricks in older Coq) produces implicit
equality constraints not caught by the previous template polymorphism
fix.

- component: template polymorphism
- introduced: same as the previous template polymorphism bug, morally
  from V8.1, first verified impacted version V8.5 (the universe
  unification is sufficiently different in V8.4 to prevent our trick
  from working)
- fixed in: expected in 8.10.2, 8.11+beta, master (#11128, Nov 2019, Gilbert)
- found by: Gilbert
- exploit: test-suite/bugs/bug_11039.v
- GH issue number: rocq-prover/rocq#11039
- risk: moderate risk (found by investigating rocq-prover/rocq#10504)

#### universe constraints erroneously discarded when forcing an asynchronous proof containing delayed monomorphic constraints inside a universe polymorphic section

- component: universe polymorphism, asynchronous proofs
- introduced: between 8.4 and 8.5 by merging the asynchronous proofs feature branch and universe polymorphism one
- impacted released versions: V8.5-V8.10
- impacted development branches: none
- impacted coqchk versions: immune
- fixed in: rocq-prover/rocq#10664
- found by: Pédrot
- exploit: no test
- GH issue number: none
- risk: unlikely to be triggered in interactive mode, not present in batch mode (i.e. coqc)

#### Set+2 incorrectly simplified to Set+1

- component: algebraic universes
- introduced: V8.10 (with the SProp commit [7550876976](https://github.com/rocq-prover/rocq/commit/75508769762372043387c67a9abe94e8f940e80a))
- impacted released versions: V8.10.0 V8.10.1 V8.10.2
- impacted coqchk versions: same
- fixed in: rocq-prover/rocq#11422
- found by: Gilbert
- exploit: see PR (custom application of Hurkens to get around the refreshing at elaboration)
- GH issue number: see PR
- risk: unlikely to be triggered through the vernacular (the system "refreshes" algebraic
    universes such that +2 increments do not appear), mild risk from plugins which manipulate
    algebraic universes.

#### variance inference for section universes ignored use of section universes in inductives and axioms defined before the inductive being inferred

- component: cumulative inductives and sections
- introduced: V8.12 ([73c3b87463](https://github.com/rocq-prover/rocq/commit/73c3b874633d6f6f8af831d4a37d0c1ae52575bc))
- impacted released versions: V8.12 to V8.15 including patch releases
- impacted coqchk versions: none
- fixed in: V8.16 rocq-prover/rocq#15950 ([118ffbc010](https://github.com/rocq-prover/rocq/commit/118ffbc010ce53ebd45baa42edd28335301ca9a5))
- found by: Gilbert and Pédrot
- exploit: see rocq-prover/rocq#15916
- risk: could be used inadvertently in developments with complex universe usage, only when using cumulative inductives declared in sections. coqchk still works.

#### Missing substitution for relevance of product domain in lazy

- component: lazy reduction, sort polymorphism
- introduced: V8.19 (with sort polymorphism, [1e7473812cec](https://github.com/rocq-prover/rocq/commit/1e7473812cec6e735394ca5f5fbefb9c78600893))
- impacted released versions: V8.19 to V9.1 including patch releases
- impacted coqchk versions: same
- fixed in: V9.2 [rocq-prover/rocq#21697](https://github.com/rocq-prover/rocq/pull/21697)
- found by: Tristan Stérin, Gaëtan Gilbert
- exploit: not fully worked out, see bug_21691.v for example error
- risk: low (needs sort polymorphism and to exploit the incorrect
  substitution from a reduction done by the kernel instead of in the
  higher layers)

#### Missing stack conversion for irrelevant-to-relevant match

- component: conversion, SProp
- introduced: V8.16 ([57081c1ae01a](https://github.com/rocq-prover/rocq/commit/57081c1ae01a742033dec44a2a42bffa08a9f5af))
  (V8.13 with the introduction of Definitional UIP for the Definitional UIP variant)
- impacted released versions: V8.16 to V9.1 including patch releases (V8.13 to V9.1 for Definitional UIP variant)
- impacted coqchk versions: same
- fixed in: V9.2 [rocq-prover/rocq#21696](https://github.com/rocq-prover/rocq/pull/21696)
- found by: Tristan Stérin, Gaëtan Gilbert
- exploit: see bug_21690.v
- risk: without Definitional UIP, believed to only contradict axioms incompatible with equality reflection (i.e. no axiom-free proof of False).
  With Definitional UIP, could be used inadvertently.

#### Incorrect discharge of sort polymorphic inductive squashing with section polymorphic sort

- component: sections, sort polymorphism
- introduced: V9.1 ([0706a177b5cb](https://github.com/rocq-prover/rocq/commit/0706a177b5cb4c829108ec8953d6087161ddb8b4))
- impacted released versions: V9.1 including patch releases
- impacted coqchk versions: none
- fixed in: V9.2 [rocq-prover/rocq#21699](https://github.com/rocq-prover/rocq/pull/21699)
- found by: Tristan Stérin, Gaëtan Gilbert
- exploit: bug_21694.v
- risk: needs a sort polymorphic inductive declared in a section with
  a section polymorphic sort and sort polymorphism in the inductive command (cf bug file)

#### Missing universe substitution in primitive array instance in lazy

- component: lazy, primitive arrays
- introduced: V8.17 ([2db83c8a7e5b](https://github.com/rocq-prover/rocq/commit/2db83c8a7e5b823d2c8d25ef07dac40b38408d3c))
- impacted released versions: V8.17 to V9.1 including patch releases
- impacted coqchk versions: same
- fixed in: V9.2 [rocq-prover/rocq#21698](https://github.com/rocq-prover/rocq/pull/21698)
- found by: Tristan Stérin, Gaëtan Gilbert
- exploit: not fully worked out, see bug_21692.v for example error
- risk: low, the instance on primitive array literals is irrelevant for conversion

#### Double universe substitution in letins from indices in match return clause

- component: conversion
- introduced: V8.14 ([d72e5c154f](https://github.com/rocq-prover/rocq/commit/d72e5c154faeea1d55387bc8c039d97f63ebd1c4))
- impacted released versions: V8.14 to V9.1 including patch releases
- impacted coqchk versions: same
- fixed in: V9.2 [rocq-prover/rocq#21688](https://github.com/rocq-prover/rocq/pull/21688)
- found by: Gaëtan Gilbert
- exploit: no full exploit known, anomaly in bug_21689.v
- risk: low (needs to use universe substitution in letin from the
  inductive indices to incorrectly convert match return clauses and
  somehow derive inconsistency from there)

#### Double universe substitution in letins from constructor arguments in match branches

- component: conversion
- introduced: V8.17 ([2db83c8a7e](https://github.com/rocq-prover/rocq/commit/2db83c8a7e5b823d2c8d25ef07dac40b38408d3c))
- impacted released versions: V8.17 to V9.2.0
- impacted coqchk versions: same
- fixed in: V9.2.1, V9.3 [rocq-prover/rocq#21972](https://github.com/rocq-prover/rocq/pull/21972)
- found by: Yann Leray
- exploit: no full exploit known, anomaly in bug_21970.v
- risk: unknown (needs to use universe substitution in letin from the
  constructor arguments to incorrectly convert branches
  and derive inconsistency from there)

### Primitive projections

#### check of guardedness of extra arguments of primitive projections missing

- component: primitive projections, guard condition
- introduced: 6 May 2014, [a4043608f](https://github.com/rocq-prover/rocq/commit/a4043608f704f026de7eb5167a109ca48e00c221), Sozeau
- impacted released versions: V8.5-V8.5pl2,
- impacted development branches: none
- impacted coqchk versions: ?
- fixed in: trunk/master/v8.5 ([ba00867d5](https://github.com/rocq-prover/rocq/commit/ba00867d515624aee734d998bfbe3880f559d907), 25 Jul 2016, Sozeau)
- found by: Sozeau, by analyzing bug report rocq-prover/rocq#4876
- exploit: to be done (?)
- GH issue number: rocq-prover/rocq#4876
- risk: consequence of bug found by chance, unlikely to be exploited by chance (MS?)

#### records based on primitive projections became possibly recursive without the guard condition being updated

- component: primitive projections, guard condition
- introduced: 10 Sep 2014, [6624459e4](https://github.com/rocq-prover/rocq/commit/6624459e492164b3d189e3518864379ff985bf8c), Sozeau (?)
- impacted released versions: V8.5
- impacted development branches: none
- impacted coqchk versions: ?
- fixed in: trunk/master/v8.5 ([120053a50](https://github.com/rocq-prover/rocq/commit/120053a50f87bd53398eedc887fa5e979f56f112), 4 Mar 2016, Dénès)
- found by: Dénès exploiting bug rocq-prover/rocq#4588
- exploit: test-suite/bugs/bug_4588.v
- GH issue number: rocq-prover/rocq#4588
- risk: ?

#### incorrect checking of subtyping with algebraic universes

- component: modules and universes
- introduced: a long time ago
- impacted released versions: ??-V8.8.0
- impacted coqchk versions: same
- fixed in: V8.8.1, V8.9.0 (#7798)
- found by: Gaëtan Gilbert
- GH issue number: rocq-prover/rocq#7695
- exploit: see issue
- risk: needs usage of explicit algebraic universe annotations, coqchk
        may catch through defunctorialization

### Conversion machines

#### the invariant justifying some optimization was wrong for some combination of sharing side effects

- component: "lazy machine" (lazy krivine abstract machine)
- introduced: prior to V7.0
- impacted released versions: V8.0-V8.0pl4, V8.1-V8.1pl3
- impacted development branches: none
- impacted coqchk versions: ([eefe63d52](https://github.com/rocq-prover/rocq/commit/eefe63d523b1b4c1b855e0f18e2574f98ff4ae64), Barras, 20 May 2008), was in beta-development for 8.2 at this time
- fixed in: master/trunk/8.2 ([f13aaec57](https://github.com/rocq-prover/rocq/commit/f13aaec57df12380323edf450aec14c372422d58) / [a8b034513](https://github.com/rocq-prover/rocq/commit/a8b034513e0c03ceb7e154949b15f62ac6862f3b), 15 May 2008, Barras), v8.1 ([e7611477a](https://github.com/rocq-prover/rocq/commit/e7611477a0a0d1b7e8c233330def46a066985cdc), 15 May 2008, Barras), v8.0 ([6ed40a8bc](https://github.com/rocq-prover/rocq/commit/6ed40a8bc000b0419f3f4731bf83d05ab5062e76), 29 Nov 2016, Herbelin, backport)
- found by: Gonthier
- exploit: by Gonthier
- GH issue number: none
- risk: unrealistic to be exploited by chance

#### collision between constructors when more than 256 constructors in a type

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- introduced: V8.1
- impacted released versions: V8.1-V8.5pl3, V8.2-V8.2pl2, V8.3-V8.3pl3, V8.4-V8.4pl5
- impacted development branches: none
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: master/trunk/v8.5 ([00894adf6](https://github.com/rocq-prover/rocq/commit/00894adf6fc11f4336a3ece0c347676bbf0b4c11) / [596a4a525](https://github.com/rocq-prover/rocq/commit/596a4a5251cc50f50bd6d25e36c81341bf65cfed), 26-39 Mar 2015, Grégoire), v8.4 ([cd2101a39](https://github.com/rocq-prover/rocq/commit/cd2101a39b3b8d58ce569761c905a5baf1dcdc86), 1 Apr 2015, Grégoire), v8.3 ([a0c7fc05b](https://github.com/rocq-prover/rocq/commit/a0c7fc05b302e38a2869c20f6db1dc376cdb59da), 1 Apr 2015, Grégoire), v8.2 ([2c6189f61](https://github.com/rocq-prover/rocq/commit/2c6189f61b85bbe1a2a56754c9effc2d7a72f16d), 1 Apr 2015, Grégoire), v8.1 ([bb877e5b5](https://github.com/rocq-prover/rocq/commit/bb877e5b54678bc34e4362fcf0315224e7c4f4cc), 29 Nov 2015, Herbelin, backport)
- found by: Dénès, Pédrot
- exploit: test-suite/bugs/bug_4157.v
- GH issue number: rocq-prover/rocq#4157
- risk:

#### wrong universe constraints

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- introduced: possibly exploitable from V8.1; exploitable at least from V8.5
- impacted released versions: V8.1-V8.4pl5 unknown, V8.5-V8.5pl3, V8.6-V8.6.1, V8.7.0-V8.7.1
- impacted development branches: unknown for v8.1-v8.4, none from v8.5
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: master ([c9f3a6cbe](https://github.com/rocq-prover/rocq/commit/c9f3a6cbe5c410256fe88580019f5c7183bab097), 12 Feb 2018, rocq-prover/rocq#6713, Dénès), v8.7 ([c058a4182](https://github.com/rocq-prover/rocq/commit/c058a4182b39460ba2b256c479a1389216c25ca9), 15 Feb 2018, Zimmermann, backport), v8.6 ([a2cc54c64](https://github.com/rocq-prover/rocq/commit/a2cc54c649c0b13190268cc5d490342d5f0cec10), 21 Feb 2018, Herbelin, backport), v8.5 ([d4d550d0f](https://github.com/rocq-prover/rocq/commit/d4d550d0f1ae5f4a8d29bbcdf991a2526ab555a6), 21 Feb 2018, Herbelin, backport)
- found by: Dénès
- exploit: test-suite/bugs/bug_6677.v
- GH issue number: rocq-prover/rocq#6677
- risk:

#### missing pops in executing 31bit arithmetic

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- introduced: V8.5
- impacted released versions: V8.1-V8.4pl5
- impacted development branches: v8.1 (probably)
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: master/trunk/v8.5 ([a5e04d9dd](https://github.com/rocq-prover/rocq/commit/a5e04d9dd178b2870b79776e1fbf1a858cdac49d), 6 Sep 2015, Dénès), v8.4 ([d5aa3bf6](https://github.com/rocq-prover/rocq/commit/d5aa3bf6fc7382e31b6f1bac58b644843d783f13), 9 Sep 2015, Dénès), v8.3 ([5da5d751](https://github.com/rocq-prover/rocq/commit/5da5d751c92df23ff3f42a04061960b287a4d3ea), 9 Sep 2015, Dénès), v8.2 ([369e82d2](https://github.com/rocq-prover/rocq/commit/369e82d2cdcd0d66d0c474dc1d062a4fc62aa24a), 9 Sep 2015, Dénès),
- found by: Catalin Hritcu
- exploit: lost?
- GH issue number: ?
- risk:

#### primitive integer emulation layer on 32 bits not robust to garbage collection

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- introduced: master (before v8.10 in GH pull request rocq-prover/rocq#6914)
- impacted released versions: none
- impacted development branches: v8.10
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: [5914313](https://github.com/rocq-prover/rocq/commit/591431312465291e85fb352a69e947eedeb2e199) (v8.10)
- found by: Roux, Melquiond
- exploit:
- GH issue number: rocq-prover/rocq#9925
- risk:

#### broken long multiplication primitive integer emulation layer on 32 bits

- component: all 3 kernel conversion machines (lazy, VM, native)
- introduced: [e43b176](https://github.com/rocq-prover/rocq/commit/e43b1768d0f8399f426b92f4dfe31955daceb1a4)
- impacted released versions: 8.10.0, 8.10.1, 8.10.2
- impacted development branches: 8.11
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: [4e176a7](https://github.com/rocq-prover/rocq/commit/4e176a7ee4660d505321ca55c5ce70a6c3d50d3b)
- found by: Soegtrop, Melquiond
- exploit: test-suite/bugs/bug_11321.v
- GH issue number: rocq-prover/rocq#11321
- risk: critical, as any BigN computation on 32-bit architectures is wrong

#### broken addmuldiv operation for large shifts

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- impacted released versions: 8.10 to 8.19
- impacted development branches: 8.20
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: [bc0adb4](https://github.com/rocq-prover/rocq/commit/bc0adb41a7c311f8d8305839c19e4812ff602720)
- found by: Martin Karup Jensen
- GH issue number: rocq-prover/rocq#19402
- risk: could be exploited by chance (though not in BigNums)

#### translation of identifier from Coq to OCaml was not bijective, leading to identify True and False

For instance `α` and `__U03b1_` were the same in the native compiler.

- component: "native" conversion machine (translation to OCaml which compiles to native code)
- introduced: V8.5
- impacted released versions: V8.5-V8.5pl1
- impacted development branches: none
- impacted coqchk versions: none (no native computation in coqchk)
- fixed in: master/trunk/v8.6 ([244d7a9aa](https://github.com/rocq-prover/rocq/commit/244d7a9aafe7ad613dd2095ca3126560cb3ea1d0), 19 May 2016, letouzey), v8.5 ([088b3161c](https://github.com/rocq-prover/rocq/commit/088b3161c93e46ec2d865fe71a206cee15acd30c), 19 May 2016, letouzey),
- found by: Letouzey, Dénès
- exploit: see commit message for [244d7a9aa](https://github.com/rocq-prover/rocq/commit/244d7a9aafe7ad613dd2095ca3126560cb3ea1d0)
- GH issue number: ?
- risk:

#### stuck primitive projections computed incorrectly by native_compute

- component: primitive projections, native_compute
- introduced: 1 Jun 2018, [e1e7888a](https://github.com/rocq-prover/rocq/commit/e1e7888ac4519f4b7470cc8469f9fd924514e352), ppedrot
- impacted released versions: 8.9.0
- impacted coqchk versions: none
- fixed in: 8.9.1 rocq-prover/rocq#9900
- found by: maximedenes exploiting bug rocq-prover/rocq#9684
- exploit: test-suite/bugs/bug_9684.v
- GH issue number: rocq-prover/rocq#9684

#### incorrect De Bruijn handling when inferring the relevance mark for a lambda

- component: lazy machine
- introduced: 2019-03-15, [23f84f37c6](https://github.com/rocq-prover/rocq/commit/23f84f37c674a07e925925b7e0d50d7ee8414093) and [71b9ad8526](https://github.com/rocq-prover/rocq/commit/71b9ad8526155020c8451dd326a52e391a9a8585), SkySkimmer
- impacted released versions: 8.10.0
- impacted coqchk versions: 8.10.0
- fixed in: 8.10.1 rocq-prover/rocq#10904
- found by: ppedrot investigating unexpected conversion failures with SProp
- exploit: test-suite/bugs/bug_10904.v
- GH issue number: rocq-prover/rocq#10904
- risk: none without using -allow-sprop (off by default in 8.10.0),
        otherwise could be exploited by mistake

#### buffer overflow on large accumulators

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- introduced: 8.1
- impacted released versions: 8.1-8.12.1
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: 8.13.0 (#13431)
- found by: Dolan, Roux, Melquiond
- GH issue number: ocaml/ocaml#6385, rocq-prover/rocq#11170
- risk: medium, as it can happen for large irreducible applications

#### buffer overflow, arbitrary code execution on floating-point operations

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- introduced: 8.13
- impacted released versions: 8.13.0
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: 8.13.1
- found by: Melquiond
- GH issue number: rocq-prover/rocq#13867
- risk: none, unless using floating-point operations; high otherwise;
        noticeable if activated by chance, since it usually breaks
        control-flow integrity

#### arbitrary code execution on irreducible PArray.set

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- introduced: 8.13
- impacted released versions: 8.13.0, 8.13.1
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: 8.13.2
- found by: Melquiond
- GH issue number: rocq-prover/rocq#13998
- risk: none, unless using primitive array operations; systematic otherwise

#### arbitrary code execution on arrays of floating point numbers

- component: "virtual" and "native" conversion machines
- introduced: 8.13
- impacted released versions: 8.13.0, 8.13.1, 8.14.0
- impacted coqchk versions: none (no VM / native computation in coqchk)
- fixed in: 8.14.1
- found by: Melquiond
- GH issue number: rocq-prover/rocq#15070
- risk: none, unless mixing open terms and primitive floats inside primitive
- arrays; critical otherwise

#### conversion of Prod / Prod values was comparing the wrong components

- component: "native" conversion machine (translation to OCaml which compiles to native code)
- introduced: V8.5
- impacted released versions: V8.5-V8.16.0 (when built with native computation enabled)
- impacted coqchk versions: none (no native computation in coqchk)
- fixed in: 8.16.1
- found by: Melquiond
- GH issue number: rocq-prover/rocq#16645
- risk: systematic

#### η-expansion of cofixpoints was performed in the wrong environment

- component: "virtual" and "native" conversion machines
- introduced: V8.9
- impacted released versions: V8.9-V8.16.0
- impacted coqchk versions: none (no VM / native computation in coqchk)
- fixed in: 8.16.1
- found by: Gaëtan Gilbert and Pierre-Marie Pédrot
- GH issue number: rocq-prover/rocq#16831
- risk: low, as it requires carefully crafted cofixpoints

#### conversion would compare the mutated version of primitive arrays instead of undoing mutation where needed

- component: all 3 kernel conversion machines (lazy, VM, native), primitive arrays
- introduced: V8.13
- impacted released versions: V8.13 to V8.16.0
- impacted coqchk versions: same
- fixed in: V8.16.1, V8.17
- found by: Maxime Buyse and Andres Erbsen
- exploit: Andres Erbsen
- GH issue number: rocq-prover/rocq#16829
- risk: some if using primitive arrays

#### tactic code could mutate a global cache of values for section variables

- component: "virtual" reduction machine
- introduced: V8.1
- impacted released versions: V8.1-V8.16.1
- impacted coqchk versions: none (no tactics in coqchk, VM only sees checked terms)
- fixed in: V8.17.0
- found by: Gaëtan Gilbert with hint from Pierre-Marie Pédrot
- GH issue number: rocq-prover/rocq#16957
- risk: the full exploitation seems to require "Definition := ltac:()"
        with change_no_check on a section variable in the ltac

#### incorrect handling of universe polymorphism

- component: VM machine
- introduced: V8.5
- impacted released versions: V8.5-V8.8.0
- impacted coqchk versions: none (no VM in coqchk)
- fixed in: V8.8.1, V8.9.0
- found by: Jason Gross
- GH issue number: rocq-prover/rocq#7723
- exploit: see issue
- risk: ??

#### Forgotten universe substitution with Register Inline on universe polymorphic definition

- component: VM and native
- introduced: V8.5
- impacted released versions: V8.5-V9.1 (all patch versions)
- impacted coqchk versions: same (only when using -bytecode-compiler yes)
- fixed in: V9.2.0
- found by: Gaëtan Gilbert
- GH issue number: rocq-prover/rocq#21736
- exploit: see issue
- risk: requires Register Inline on universe polymorphic constant
- additional note: does not seem to be exploitable before 8.8 (until 8.6 Register
  Inline fails with anomaly on universe polymorphic constants, and before
  8.8 Register Inline only affects native which fails in ocamlopt)

#### conversion under contexts is done in the wrong environment

- component: lazy conversion
- introduced: 8.14 ([d72e5c154f, PR #13563](https://github.com/rocq-prover/rocq/pull/13563))
- impacted versions: until 9.2.0 (included)
- impacted coqchk versions: same
- fixed in: 9.2.1, 9.3.0 ([rocq-prover/rocq#22379](https://github.com/rocq-prover/rocq/pull/22379))
- found by: Daniel Selsam
- GH issue number: ([rocq-prover/rocq#22378](https://github.com/rocq-prover/rocq/pull/22378))
- exploit: see issue
- risk: ?

### Side-effects

#### polymorphic side-effects inside monomorphic definitions incorrectly handled as not inlined

- component: side-effects
- introduced: ?
- impacted released versions: at least from 8.6 to 8.12.0
- impacted coqchk versions: none (no side-effects in the checker)
- fixed in: V8.12.1 (rocq-prover/rocq#13331)
- found by: ppedrot
- exploit: test-suite/bugs/bug_13330.v
- GH issue number: rocq-prover/rocq#13330
- risk: unlikely to be exploited by mistake, requires the use of unsafe tactics

#### Section variables used in side effects not checked by Proof using

- component: side-effects / sections
- introduced: 8.11
- impacted released versions: from 8.11.0 to 8.20.0
- impacted coqchk versions: none (no side-effects in the checker)
- fixed in: V9.0 (rocq-prover/rocq#19476)
- found by: Pierre Courtieu
- exploit: test-suite/output/bug_19861.v
- GH issue number: rocq-prover/rocq#19861
- risk: requires incorrect `Proof using` and no use of coqchk

### Forgetting unsafe flags

#### unsafe typing flags used inside a section would not be reported by Print Assumptions after closing the section

- component: sections
- introduced: [abab878b8d](https://github.com/rocq-prover/rocq/commit/abab878b8d8b5ca85a4da688abed68518f0b17bd) (#10291, 8.11), technically available earlier through plugins
- impacted coqchk versions: none (coqchk rejects affected files)
- fixed in: 8.14 rocq-prover/rocq#14395
- found by: Anton Trunov
- GH issue number: rocq-prover/rocq#14317
- risk: low as it needs the use of explicit unsafe flags

### Conflicts with axioms in library

#### axiom of description and decidability of equality on real numbers in library Reals was inconsistent with impredicative Set

- component: library of real numbers
- introduced: [67c75fa01](https://github.com/rocq-prover/rocq/commit/67c75fa01adbbe1d4e39eff2b930ad168510072c), 20 Jun 2002
- impacted released versions: 7.3.1, 7.4
- impacted coqchk versions:
- fixed by deciding to drop impredicativity of Set: [bac707973](https://github.com/rocq-prover/rocq/commit/bac707973955ef64eadae24ea01e029a5394626e), 28 Oct 2004
- found by: Herbelin & Werner
- exploit: need to find the example again
- GH issue number: no
- risk: unlikely to be exploited by chance

#### guard condition was unknown to be inconsistent with propositional extensionality in library Sets

- component: library of extensional sets, guard condition
- introduced: not a bug per se but an incompatibility discovered late
- impacted released versions: technically speaking from V6.1 with the introduction of the Sets library which was then inconsistent from the very beginning without we knew it
- impacted coqchk versions: ?
- fixed by constraining the guard condition: ([9b272a8](https://github.com/rocq-prover/rocq/commit/9b272a861bc3263c69b699cd2ac40ab2606543fa), [ccd7546c](https://github.com/rocq-prover/rocq/commit/ccd7546cd32c8a7901a4234f86aa23b4a7e1a043) 28 Oct 2014, Barras, Dénès)
- found by: Schepler, Dénès, Azevedo de Amorim
- exploit: ?
- GH issue number: none
- risk: unlikely to be exploited by chance (?)

#### incompatibility axiom of choice and excluded-middle with elimination of large singletons to Set

- component: library for axiom of choice and excluded-middle
- introduced: not a bug but a change of intended "model"
- impacted released versions: strictly before 8.1
- impacted coqchk versions: ?
- fixed by constraining singleton elimination: [b19397ed8](https://github.com/rocq-prover/rocq/commit/b19397ed88ef8aa1ea1ca228b5d23b94e15f419f), r9633, 9 Feb 2007, Herbelin
- found by: Benjamin Werner
- exploit:
- GH issue number: none
- risk:

#### Incorrect specification of PrimFloat.leb

- component: primitive floating-points
- introduced: 8.11
- impacted released versions: 8.11.0, 8.11.1, 8.11.2
- fixed by fixing the spec: rocq-prover/rocq#12484
- found by: Pierre Roux
- exploit: test-suite/bugs/bug_12483.v
- GH issue number: rocq-prover/rocq#12483
- risk: proof of false when using the incorrect axiom

#### Incorrect implementation of SFclassify.

- component: floating-point library
- introduced: 8.11
- impacted released versions: 8.11.0-8.15.1
- fixed by fixing the implementation: rocq-prover/rocq#16101
- found by: François Bobot
- exploit: test-suite/bugs/bug_16096.v
- GH_issue_number: rocq-prover/rocq#16096
- risk: proof of false when using the axioms in Floats.Axioms.

#### nativenorm reading back closures as arbitrary floating-point values

- component: primitive floating-points + "native" conversion machine (translation to OCaml which compiles to native code)
- introduced: 8.11
- impacted released versions: 8.11.0-8.17.1
- impacted coqchk versions: none (no native computation in coqchk)
- fixed in: 8.18.0
- found by: Jason Gross
- GH issue number: rocq-prover/rocq#17871
- risk: proof of false when using primitive floats and native_compute

#### guard condition issue made it inconsistent with propositional extensionality in library Sets

- component: library of extensional sets, guard condition
- introduced: variant of [the issue with propositional extensionality](#guard-condition-was-unknown-to-be-inconsistent-with-propositional-extensionality-in-library-Sets) that was not fixed then
- impacted released versions: the relative inconsistency was present from the very beginning, until 9.0
- impacted coqchk versions: *-9.0
- fixed in: 9.0.1
- fixed by further constraining the guard condition: [PR 21050](https://github.com/rocq-prover/rocq/pull/21050)
- found by: Thomas Lamiaux, Yann Leray, Pierre-Marie Pédrot, Nicolas Tabareau
- GH issue number: [21053](https://github.com/rocq-prover/issues/21053)
- risk: unlikely to be exploited by chance (?)

### Deserialization

#### deserialization of .vo data not properly checked

- component: coqchk (coqc trusts that .vo files are well formed)
- introduced: 8.16 (univ levels), 8.10 (retroknowledge)
- impacted released versions: 8.10-8.18.1
- impacted coqchk versions: same
- fixed in: 8.19
- found by: Mario Carneiro
- GH issue number: N/A (fix pull requests: rocq-prover/rocq#18403, rocq-prover/rocq#18406)
- risk: can lead to segfaults or arbitrary code execution on crafted .vo files
    (files produced by coqc are fine)

There were otherwise several bugs in beta-releases, from memory, bugs with beta versions of primitive projections or template polymorphism or native compilation or guard (e7fc96366, 2a4d714a1).

## Probably non exploitable fixed bugs

There were otherwise maybe unexploitable kernel bugs, e.g. 2df88d83
(Require overloading), 0adf0838 ("Univs: uncovered bug in
strengthening of opaque polymorphic definitions."), 5122a398 (#3746
about functors), rocq-prover/rocq#4346 (casts in VM), a14bef4 (guard condition in
8.1), 6ed40a8 ("Georges' bug" with ill-typed lazy machine), and
various other bugs in 8.0 or 8.1 without knowing if they are critical.

#### bug in 31bit arithmetic

- component: "virtual machine" (compilation to bytecode ran by a C-interpreter)
- introduced: V8.1
- impacted released versions: none
- impacted development branches:
- impacted coqchk versions: none (no virtual machine in coqchk)
- fixed in: master/trunk/v8.5 (0f8d1b92c, 6 Sep 2015, Dénès)
- found by: Dénès, from a bug report by Tahina Ramananandro
- exploit: non exploitable?
- GH issue number: ?
- risk:
