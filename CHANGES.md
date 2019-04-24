Unreleased changes
==================

OCaml and dependencies

- Coq 8.10 requires OCaml >= 4.05.0, bumped from 4.02.3 See the
  INSTALL file for more information on dependencies.

- Coq 8.10 doesn't need Camlp5 to build anymore. It now includes a
  fork of the core parsing library that Coq uses, which is a small
  subset of the whole Camlp5 distribution. In particular, this subset
  doesn't depend on the OCaml AST, allowing easier compilation and
  testing on experimental OCaml versions.

  The Coq developers would like to thank Daniel de Rauglaudre for many
  years of continued support.

Coqide

- CoqIDE now depends on gtk+3 and lablgtk3, rather than gtk+2 and lablgtk2.

- CoqIDE now properly sets the module name for a given file based on
  its path, see -topfile change entry for more details.

- Preferences from coqide.keys are no longer overridden by modifiers
  preferences in coqiderc.

Coqtop

- the use of `coqtop` as a compiler has been deprecated, in favor of
  `coqc`. Consequently option `-compile` will stop to be accepted in
  the next release. `coqtop` is now reserved to interactive
  use. (@ejgallego #9095)

- new option -topfile filename, which will set the current module name
  (à la -top) based on the filename passed, taking into account the
  proper -R/-Q options. For example, given -R Foo foolib using
  -topfile foolib/bar.v will set the module name to Foo.Bar.

Specification language, type inference

- Fixing a missing check in interpreting instances of existential
  variables that are bound to local definitions might exceptionally
  induce an overhead if the cost of checking the conversion of the
  corresponding definitions is additionally high (PR #8215).

- A few improvements in inference of the return clause of `match` can
  exceptionally introduce incompatibilities (PR #262). This can be
  solved by writing an explicit `return` clause, sometimes even simply
  an explicit `return _` clause.

- Using non-projection values with the projection syntax is not
  allowed. For instance "0.(S)" is not a valid way to write "S 0".
  Projections from non-primitive (emulated) records are allowed with
  warning "nonprimitive-projection-syntax".

Kernel

- Added primitive integers

- Unfolding heuristic in termination checking made more complete.
  In particular Coq is now more aggressive in unfolding constants
  when it looks for a iota redex. Performance regression may occur
  in Fixpoint declarations without an explicit {struct} annotation,
  since guessing the decreasing argument can now be more expensive.
  (PR #9602)

Notations

- New command `Declare Scope` to explicitly declare a scope name
  before any use of it. Implicit declaration of a scope at the time of
  `Bind Scope`, `Delimit Scope`, `Undelimit Scope`, or `Notation` is
  deprecated.

- New command `String Notation` to register string syntax for custom
  inductive types.

- Numeral notations now parse decimal constants such as 1.02e+01 or
  10.2. Parsers added for Q and R. This should be considered as an
  experimental feature currently.
  Note: in -- the rare -- case when such numeral notations were used
  in a development along with Q or R, they may have to be removed or
  deconflicted through explicit scope annotations (1.23%Q,
  45.6%R,...).

- Various bugs have been fixed (e.g. PR #9214 on removing spurious
  parentheses on abbreviations shortening a strict prefix of an application).

- Numeral Notations now support inductive types in the input to
  printing functions (e.g., numeral notations can be defined for terms
  containing things like `@cons nat O O`), and parsing functions now
  fully normalize terms including parameters of constructors (so that,
  e.g., a numeral notation whose parsing function outputs a proof of
  `Nat.gcd x y = 1` will no longer fail to parse due to containing the
  constant `Nat.gcd` in the parameter-argument of `eq_refl`).  See
  #9840 for more details.

- Deprecated compatibility notations have actually been removed.  Uses
  of these notations are generally easy to fix thanks to the hint
  contained in the deprecation warnings. For projects that require
  more than a handful of such fixes, there is [a
  script](https://gist.github.com/JasonGross/9770653967de3679d131c59d42de6d17#file-replace-notations-py)
  that will do it automatically, using the output of coqc. The script
  contains documentation on its usage in a comment at the top.

Plugins

- The quote plugin (https://coq.inria.fr/distrib/V8.8.1/refman/proof-engine/detailed-tactic-examples.html#quote)
  was removed. If some users are interested in maintaining this plugin
  externally, the Coq development team can provide assistance for extracting
  the plugin and setting up a new repository.

Tactics

- Removed the deprecated `romega` tactics.
- Tactic names are no longer allowed to clash, even if they are not defined in
  the same section. For example, the following is no longer accepted:
  `Ltac foo := idtac. Section S. Ltac foo := fail. End S.`

- The tactics 'lia','nia','lra','nra' are now using a novel
  Simplex-based proof engine. In case of regression, 'Unset Simplex'
  to get the venerable Fourier-based engine.

- Names of existential variables occurring in Ltac functions
  (e.g. `?[n]` or `?n` in terms - not in patterns) are now interpreted
  the same way as other variable names occurring in Ltac functions.

- Hint declaration and removal should now specify a database (e.g. `Hint Resolve
  foo : database`). When the database name is omitted, the hint is added to the
  core database (as previously), but a deprecation warning is emitted.

- There are now tactics in `PreOmega.v` called
  `Z.div_mod_to_equations`, `Z.quot_rem_to_equations`, and
  `Z.to_euclidean_division_equations` (which combines the `div_mod`
  and `quot_rem` variants) which allow `lia`, `nia`, `romega`, etc to
  support `Z.div` and `Z.modulo` (`Z.quot` and `Z.rem`, respectively),
  by posing the specifying equation for `Z.div` and `Z.modulo` before
  replacing them with atoms.

- Ltac backtraces can be turned on using the "Ltac Backtrace" option.

- The syntax of the `autoapply` tactic was fixed to conform with preexisting
  documentation: it now takes a `with` clause instead of a `using` clause.



Vernacular commands

- `Combined Scheme` can now work when inductive schemes are generated in sort
  `Type`. It used to be limited to sort `Prop`.

- Binders for an `Instance` now act more like binders for a `Theorem`.
  Names may not be repeated, and may not overlap with section variable names.

- Removed the deprecated `Implicit Tactic` family of commands.

- The `Automatic Introduction` option has been removed and is now the
  default.

- `Arguments` now accepts names for arguments provided with `extra_scopes`.

- The naming scheme for anonymous binders in a `Theorem` has changed to
  avoid conflicts with explicitly named binders.

- Computation of implicit arguments now properly handles local definitions in the
  binders for an `Instance`, and can be mixed with implicit binders `{x : T}`.

- `Declare Instance` now requires an instance name.

- Option `Refine Instance Mode` has been turned off by default, meaning that
  `Instance` no longer opens a proof when a body is provided.

- `Instance`, when no body is provided, now always opens a proof. This is a
   breaking change, as instance of `Instance foo : C.` where `C` is a trivial
   class will have to be changed into `Instance foo : C := {}.` or
   `Instance foo : C. Proof. Qed.`.

- Option `Program Mode` now means that the `Program` attribute is enabled
  for all commands that support it. In particular, it does not have any effect
  on tactics anymore. May cause some incompatibilities.

- The algorithm computing implicit arguments now behaves uniformly for primitive
  projection and application nodes (bug #9508).

- `Hypotheses` and `Variables` can now take implicit binders inside sections.

- Removed deprecated option `Automatic Coercions Import`.

- The `Show Script` command has been deprecated.

- Option `Refine Instance Mode` has been deprecated and will be removed in
  the next version.

- `Coercion` does not warn ambiguous paths which are obviously convertible with
  existing ones.

- A new flag `Fast Name Printing` has been introduced. It changes the
  algorithm used for allocating bound variable names for a faster but less
  clever one.

Tools

- The `-native-compiler` flag of `coqc` and `coqtop` now takes an argument which can have three values:
  - `no` disables native_compute
  - `yes` enables native_compute and precompiles `.v` files to native code
  - `ondemand` enables native_compute but compiles code only when `native_compute` is called

  The default value is `ondemand`.

  Note that this flag now has priority over the configure flag of the same name.

- A new `-bytecode-compiler` flag for `coqc` and `coqtop` controls whether
  conversion can use the VM. The default value is `yes`.

- CoqIDE now supports input for Unicode characters. For example, typing
  "\alpha" then the "Shift+Space" will insert the greek letter alpha.
  In fact, typing the prefix string "\a" is sufficient.
  A larger number of default bindings are provided, following the latex
  naming convention. Bindings can be customized, either globally, or on a
  per-project basis, with the requirement is that keys must begin with a
  backslash and contain no space character. Bindings may be assigned custom
  priorities, so that prefixes resolve to the most convenient bindings.
  The documentation pages for CoqIDE provides further details.

- The pretty timing diff scripts (flag `TIMING=1` to a
  `coq_makefile`-made `Makefile`, also
  `tools/make-both-single-timing-files.py`,
  `tools/make-both-time-files.py`, and `tools/make-one-time-file.py`)
  now correctly support non-UTF-8 characters in the output of
  `coqc`/`make` as well as printing to stdout, on both python2 and
  python3.

- Coq options can be set on the command line, eg `-set "Universe Polymorphism=true"`

- coq_makefile's install target now errors if any file to install is missing.

Standard Library

- Added lemmas about monotonicity of `N.double` and `N.succ_double`, and about
  the upper bound of number represented by a vector.
  Allowed implicit vector length argument in `Ndigits.Bv2N`.

- Added `Bvector.BVeq` that decides whether two `Bvector`s are equal.

- Added notations for `BVxor`, `BVand`, `BVor`, `BVeq` and `BVneg`.

- Added `ByteVector` type that can convert to and from [string].

- The prelude used to be automatically Exported and is now only
  Imported. This should be relevant only when importing files which
  don't use -noinit into files which do.

- Added `Coq.Structures.OrderedTypeEx.String_as_OT` to make strings an
  ordered type (using lexical order).

- The `Coq.Numbers.Cyclic.Int31` library is deprecated.

- Added lemmas about `Z.testbit`, `Z.ones`, and `Z.modulo`.

- Moved the `auto` hints of the `FSet` library into a new
  `fset` database.

Universes

- Added `Print Universes Subgraph` variant of `Print Universes`.
  Try for instance `Print Universes Subgraph(sigT2.u1 sigT_of_sigT2.u1 projT3_eq.u1 eq_sigT2_rect.u1).`

- Added private universes for opaque polymorphic constants, see doc
  for the "Private Polymorphic Universes" option (and Unset it to get
  the previous behaviour).

SProp

- Added a universe "SProp" for definitionally proof irrelevant
  propositions. Use with -allow-sprop. See manual for details.

Inductives

- An option and attributes to control the automatic decision to
  declare an inductive type as template polymorphic were added.
  Warning "auto-template" will trigger when an inductive is
  automatically declared template polymorphic without the attribute.

Funind

- Inductive types declared by Funind will never be template polymorphic.

Misc

- Option "Typeclasses Axioms Are Instances" is deprecated. Use Declare Instance for axioms which should be instances.

- Removed option "Printing Primitive Projection Compatibility"

SSReflect

- New tactic `under` to rewrite under binders, given an extensionality lemma:
  - interactive mode: `under lem`, associated terminator: `over`
  - one-liner mode: `under lem do [tac1 | ...]`

  It can take occurrence switches, contextual patterns, and intro patterns:
  `under {2}[in RHS]eq_big => [i|i ?] do ...`.

  See the reference manual for the actual documentation.

- New intro patterns:
  - temporary introduction: `=> +`
  - block introduction: `=> [^ prefix ] [^~ suffix ]`
  - fast introduction: `=> >`
  - tactics as views: `=> /ltac:mytac`
  - replace hypothesis: `=> {}H`

  See the reference manual for the actual documentation.

- Clear discipline made consistent across the entire proof language.
  Whenever a clear switch `{x..}` comes immediately before an existing proof
  context entry (used as a view, as a rewrite rule or as name for a new
  context entry) then such entry is cleared too.

  E.g. The following sentences are elaborated as follows (when H is an existing
  proof context entry):
  - `=> {x..} H`       ->  `=> {x..H} H`
  - `=> {x..} /H`      ->  `=> /v {x..H}`
  - `rewrite {x..} H`  ->  `rewrite E {x..H}`

- `inE` now expands `y \in r x` when `r` is a `simpl_rel`.

- New `{pred T}` notation for a `pred T` alias in the `pred_sort` coercion
  class, simplified `predType` interface: `pred_class` and `mkPredType`
  deprecated, `{pred T}` and `PredType` should be used instead.

- `if c return t then ...` now expects `c` to be a variable bound in `t`.

- New `nonPropType` interface matching types that do _not_ have sort `Prop`.

- New `relpre R f` definition for the preimage of a relation R under f.

Diffs

- Some error messages that show problems with a pair of non-matching values will now
  highlight the differences.
