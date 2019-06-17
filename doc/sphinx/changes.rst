--------------
Recent changes
--------------

.. ifconfig:: not coq_config.is_a_released_version

   .. include:: ../unreleased.rst

Version 8.10
------------

Summary of changes
~~~~~~~~~~~~~~~~~~

|Coq| version 8.10 contains two major new features: support for a native
fixed-precision integer type and a new sort :math:`\SProp` of strict
propositions. It is also the result of refinements and stabilization of
previous features, deprecations or removals of deprecated features,
cleanups of the internals of the system and API, and many documentation improvements.
This release includes many user-visible changes, including deprecations that are
documented in the next subsection, and new features that are documented in the
reference manual. Here are the most important user-visible changes:

- Kernel:

  - A notion of primitive object was added to the calculus. Its first
    instance is primitive cyclic unsigned integers, axiomatized in
    module :g:`UInt63`. See Section :ref:`primitive-integers`.
    The `Coq.Numbers.Cyclic.Int31` library is deprecated
    (`#6914 <https://github.com/coq/coq/pull/6914>`_, by Maxime Dénès,
    Benjamin Grégoire and Vincent Laporte,
    with help and reviews from many others).

  - The :math:`\SProp` sort of definitionally proof-irrelevant propositions was
    introduced. :math:`\SProp` allows to mark proof
    terms as irrelevant for conversion, and is treated like :math:`\Prop`
    during extraction. It is enabled using the `-allow-sprop`
    command-line flag or the :flag:`Allow StrictProp` flag.
    See Chapter :ref:`sprop`
    (`#8817 <https://github.com/coq/coq/pull/8817>`_, by Gaëtan Gilbert).

  - The unfolding heuristic in termination checking was made more
    complete, allowing more constants to be unfolded to discover valid
    recursive calls.  Performance regression may occur in Fixpoint
    declarations without an explicit ``{struct}`` annotation, since
    guessing the decreasing argument can now be more expensive
    (`#9602 <https://github.com/coq/coq/pull/9602>`_, by Enrico Tassi).

- Universes:

  - Added :cmd:`Print Universes Subgraph` variant of :cmd:`Print Universes`.
    Try for instance
    :g:`Print Universes Subgraph(sigT2.u1 sigT_of_sigT2.u1 projT3_eq.u1).`
    (`#8451 <https://github.com/coq/coq/pull/8451>`_, by Gaëtan Gilbert).

  - Added private universes for opaque polymorphic constants, see the
    documentation for the :flag:`Private Polymorphic Universes` flag,
    and unset it to get the previous behaviour
    (`#8850 <https://github.com/coq/coq/pull/8850>`_, by Gaëtan Gilbert).

- Notations:

  - New command :cmd:`String Notation` to register string syntax for custom
    inductive types
    (`#8965 <https://github.com/coq/coq/pull/8965>`_, by Jason Gross).

  - Experimental: :ref:`Numeral Notations <numeral-notations>` now parse decimal
    constants such as ``1.02e+01`` or ``10.2``. Parsers added for :g:`Q` and :g:`R`.
    In the rare case when such numeral notations were used
    in a development along with :g:`Q` or :g:`R`, they may have to be removed or
    disambiguated through explicit scope annotations
    (`#8764 <https://github.com/coq/coq/pull/8764>`_, by Pierre Roux).

- Ltac backtraces can be turned on using the :flag:`Ltac Backtrace`
  flag, which is off by default
  (`#9142 <https://github.com/coq/coq/pull/9142>`_,
  fixes `#7769 <https://github.com/coq/coq/issues/7769>`_
  and `#7385 <https://github.com/coq/coq/issues/7385>`_,
  by Pierre-Marie Pédrot).

- The tactics :tacn:`lia`, :tacn:`nia`, :tacn:`lra`, :tacn:`nra` are now using a novel
  Simplex-based proof engine. In case of regression, unset :flag:`Simplex`
  to get the venerable Fourier-based engine
  (`#8457 <https://github.com/coq/coq/pull/8457>`_, by Fréderic Besson).

- SSReflect:

  - New intro patterns:

    - temporary introduction: `=> +`
    - block introduction: `=> [^ prefix ] [^~ suffix ]`
    - fast introduction: `=> >`
    - tactics as views: `=> /ltac:mytac`
    - replace hypothesis: `=> {}H`

      See Section :ref:`introduction_ssr`
      (`#6705 <https://github.com/coq/coq/pull/6705>`_, by Enrico Tassi,
      with help from Maxime Dénès,
      ideas coming from various users).

  - New tactic :tacn:`under` to rewrite under binders, given an
    extensionality lemma:

    - interactive mode: :n:`under @term`, associated terminator: :tacn:`over`
    - one-liner mode: `under @term do [@tactic | ...]`

    It can take occurrence switches, contextual patterns, and intro patterns:
    :g:`under {2}[in RHS]eq_big => [i|i ?] do ...`
    (`#9651 <https://github.com/coq/coq/pull/9651>`_,
    by Erik Martin-Dorel and Enrico Tassi).

- :cmd:`Combined Scheme` now works when inductive schemes are generated in sort
  :math:`\Type`. It used to be limited to sort `Prop`
  (`#7634 <https://github.com/coq/coq/pull/7634>`_, by Théo Winterhalter).

- A new registration mechanism for reference from ML code to Coq
  constructs has been added
  (`#186 <https://github.com/coq/coq/pull/186>`_,
  by Emilio Jesús Gallego Arias, Maxime Dénès and Vincent Laporte).

- CoqIDE:

  - CoqIDE now depends on gtk+3 and lablgtk3 instead of gtk+2 and lablgtk2.
    The INSTALL file available in the Coq sources has been updated to list
    the new dependencies
    (`#9279 <https://github.com/coq/coq/pull/9279>`_,
    by Hugo Herbelin, with help from Jacques Garrigue,
    Emilio Jesús Gallego Arias, Michael Sogetrop and Vincent Laporte).

  - Smart input for Unicode characters. For example, typing
    ``\alpha`` then ``Shift+Space`` will insert the greek letter alpha.
    A larger number of default bindings are provided, following the latex
    naming convention. Bindings can be customized, either globally, or on a
    per-project basis. See Section :ref:`coqide-unicode` for details
    (`#8560 <https://github.com/coq/coq/pull/8560>`_, by Arthur Charguéraud).

- Infrastructure and dependencies:

  - Coq 8.10 requires OCaml >= 4.05.0, bumped from 4.02.3 See the
    `INSTALL` file for more information on dependencies
    (`#7522 <https://github.com/coq/coq/pull/7522>`_, by Emilio Jesús Gallego Arías).

  - Coq 8.10 doesn't need Camlp5 to build anymore. It now includes a
    fork of the core parsing library that Coq uses, which is a small
    subset of the whole Camlp5 distribution. In particular, this subset
    doesn't depend on the OCaml AST, allowing easier compilation and
    testing on experimental OCaml versions. Coq also ships a new parser
    `coqpp` that plugin authors must switch to
    (`#7902 <https://github.com/coq/coq/pull/7902>`_,
    `#7979 <https://github.com/coq/coq/pull/7979>`_,
    `#8161 <https://github.com/coq/coq/pull/8161>`_,
    `#8667 <https://github.com/coq/coq/pull/8667>`_,
    and `#8945 <https://github.com/coq/coq/pull/8945>`_,
    by Pierre-Marie Pédrot and Emilio Jesús Gallego Arias).

    The Coq developers would like to thank Daniel de Rauglaudre for many
    years of continued support.

  - Coq now supports building with Dune, in addition to the traditional
    Makefile which is scheduled for deprecation
    (`#6857 <https://github.com/coq/coq/pull/6857>`_,
    by Emilio Jesús Gallego Arias, with help from Rudi Grinberg).

    Experimental support for building Coq projects has been integrated
    in Dune at the same time, providing an `improved experience
    <https://coq.discourse.group/t/a-guide-to-building-your-coq-libraries-and-plugins-with-dune/>`_
    for plugin developers. We thank the Dune team for their work
    supporting Coq.

Version 8.10 also comes with a bunch of smaller-scale changes and
improvements regarding the different components of the system, including
many additions to the standard library (see the next subsection for details).

On the implementation side, the ``dev/doc/changes.md`` file documents
the numerous changes to the implementation and improvements of
interfaces. The file provides guidelines on porting a plugin to the new
version and a plugin development tutorial originally made by Yves Bertot
is now in `doc/plugin_tutorial`. The ``dev/doc/critical-bugs`` file
documents the known critical bugs of |Coq| and affected releases.

The efficiency of the whole system has seen improvements thanks to
contributions from Gaëtan Gilbert, Pierre-Marie Pédrot, and Maxime Dénès.

Maxime Dénès, Emilio Jesús Gallego Arias, Gaëtan Gilbert, Michael
Soegtrop, Théo Zimmermann worked on maintaining and improving the
continuous integration system and package building infrastructure.
Coq is now continuously tested against OCaml trunk, in addition to the
oldest supported and latest OCaml releases.

Coq's documentation for the development branch is now deployed
continuously at https://coq.github.io/doc/master/api (documentation of
the ML API), https://coq.github.io/doc/master/refman (reference
manual), and https://coq.github.io/doc/master/stdlib (documentation of
the standard library). Similar links exist for the `v8.10` branch.

The OPAM repository for |Coq| packages has been maintained by Guillaume
Melquiond, Matthieu Sozeau, Enrico Tassi (who migrated it to opam 2)
with contributions from many users. A list of packages is available at
https://coq.inria.fr/opam/www/.

The 61 contributors to this version are David A. Dalrymple, Tanaka
Akira, Benjamin Barenblat, Yves Bertot, Frédéric Besson, Lasse
Blaauwbroek, Martin Bodin, Joachim Breitner, Tej Chajed, Frédéric
Chapoton, Arthur Charguéraud, Cyril Cohen, Lukasz Czajka, Christian
Doczkal, Maxime Dénès, Andres Erbsen, Jim Fehrle, Gaëtan Gilbert, Matěj
Grabovský, Simon Gregersen, Jason Gross, Samuel Gruetter, Hugo Herbelin,
Jasper Hugunin, Mirai Ikebuchi, Emilio Jesus Gallego Arias, Chantal
Keller, Matej Košík, Vincent Laporte, Olivier Laurent, Larry Darryl Lee
Jr, Pierre Letouzey, Nick Lewycky, Yao Li, Yishuai Li, Xia Li-yao, Assia
Mahboubi, Simon Marechal, Erik Martin-Dorel, Thierry Martinez, Guillaume
Melquiond, Kayla Ngan, Sam Pablo Kuper, Karl Palmskog, Clément
Pit-Claudel, Pierre-Marie Pédrot, Pierre Roux, Kazuhiko Sakaguchi, Ryan
Scott, Vincent Semeria, Gan Shen, Michael Soegtrop, Matthieu Sozeau,
Enrico Tassi, Laurent Théry, Kamil Trzciński, whitequark, Théo
Winterhalter, Beta Ziliani and Théo Zimmermann.

Many power users helped to improve the design of the new features via
the issue and pull request system, the |Coq| development mailing list,
the coq-club@inria.fr mailing list or the new Discourse forum. It would
be impossible to mention exhaustively the names of everybody who to some
extent influenced the development.

Version 8.10 is the fifth release of |Coq| developed on a time-based
development cycle. Its development spanned 6 months from the release of
|Coq| 8.9. Vincent Laporte is the release manager and maintainer of this
release. This release is the result of ~2500 commits and ~650 PRs merged,
closing 150+ issues.

| Santiago de Chile, April 2019,
| Matthieu Sozeau for the |Coq| development team
|

Other changes in 8.10+beta1
~~~~~~~~~~~~~~~~~~~~~~~~~~~

- Command-line tools and options:

  - The use of `coqtop` as a compiler has been deprecated, in favor of
    `coqc`. Consequently option `-compile` will stop to be accepted in
    the next release. `coqtop` is now reserved to interactive
    use
    (`#9095 <https://github.com/coq/coq/pull/9095>`_,
    by Emilio Jesús Gallego Arias).

  - New option ``-topfile filename``, which will set the current module name
    (*à la* ``-top``) based on the filename passed, taking into account the
    proper ``-R``/``-Q`` options. For example, given ``-R Foo foolib`` using
    ``-topfile foolib/bar.v`` will set the module name to ``Foo.Bar``.
    CoqIDE now properly sets the module name for a given file based on
    its path
    (`#8991 <https://github.com/coq/coq/pull/8991>`_,
    closes `#8989 <https://github.com/coq/coq/issues/8989>`_,
    by Gaëtan Gilbert).

  - Experimental: Coq flags and options can now be set on the
    command-line, e.g. ``-set "Universe Polymorphism=true"``
    (`#9876 <https://github.com/coq/coq/pull/9876>`_, by Gaëtan Gilbert).

  - The `-native-compiler` flag of `coqc` and `coqtop` now takes an
    argument which can have three values:

    - `no` disables native_compute
    - `yes` enables native_compute and precompiles `.v` files to
      native code
    - `ondemand` enables native_compute but compiles code only when
      `native_compute` is called

    The default value is `ondemand`. Note that this flag now has
    priority over the configure flag of the same name.

    A new `-bytecode-compiler` flag for `coqc` and `coqtop` controls
    whether conversion can use the VM. The default value is `yes`.

    (`#8870 <https://github.com/coq/coq/pull/8870>`_, by Maxime Dénès)

  - The pretty timing diff scripts (flag `TIMING=1` to a
    `coq_makefile`\-made `Makefile`, also
    `tools/make-both-single-timing-files.py`,
    `tools/make-both-time-files.py`, and `tools/make-one-time-file.py`)
    now correctly support non-UTF-8 characters in the output of
    `coqc` / `make` as well as printing to stdout, on both python2 and
    python3
    (`#9872 <https://github.com/coq/coq/pull/9872>`_,
    closes `#9767 <https://github.com/coq/coq/issues/9767>`_
    and `#9705 <https://github.com/coq/coq/issues/9705>`_,
    by Jason Gross)

  - coq_makefile's install target now errors if any file to install is missing
    (`#9906 <https://github.com/coq/coq/pull/9906>`_, by Gaëtan Gilbert).

  - Preferences from ``coqide.keys`` are no longer overridden by
    modifiers preferences in ``coqiderc``
    (`#10014 <https://github.com/coq/coq/pull/10014>`_, by Hugo Herbelin).

- Specification language, type inference:

  - Fixing a missing check in interpreting instances of existential
    variables that are bound to local definitions. Might exceptionally
    induce an overhead if the cost of checking the conversion of the
    corresponding definitions is additionally high
    (`#8217 <https://github.com/coq/coq/pull/8217>`_,
    closes `#8215 <https://github.com/coq/coq/issues/8215>`_,
    by Hugo Herbelin).

  - A few improvements in inference of the return clause of `match` that
    can exceptionally introduce incompatibilities. This can be
    solved by writing an explicit `return` clause, sometimes even simply
    an explicit `return _` clause
    (`#262 <https://github.com/coq/coq/pull/262>`_, by Hugo Herbelin).

  - Using non-projection values with the projection syntax is not
    allowed. For instance :g:`0.(S)` is not a valid way to write :g:`S 0`.
    Projections from non-primitive (emulated) records are allowed with
    warning "nonprimitive-projection-syntax"
    (`#8829 <https://github.com/coq/coq/pull/8829>`_, by Gaëtan Gilbert).

  - An option and attributes to control the automatic decision to declare
    an inductive type as template polymorphic were added.  Warning
    "auto-template" (off by default) can trigger when an inductive is
    automatically declared template polymorphic without the attribute.

    Inductive types declared by Funind will never be template polymorphic.

    (`#8488 <https://github.com/coq/coq/pull/8488>`_, by Gaëtan Gilbert)

- Notations:

  - New command :cmd:`Declare Scope` to explicitly declare a scope name
    before any use of it. Implicit declaration of a scope at the time of
    :cmd:`Bind Scope`, :cmd:`Delimit Scope`, :cmd:`Undelimit Scope`,
    or :cmd:`Notation` is deprecated
    (`#7135 <https://github.com/coq/coq/pull/7135>`_, by Hugo Herbelin).

  - Various bugs have been fixed (e.g. `#9214
    <https://github.com/coq/coq/pull/9214>`_ on removing spurious
    parentheses on abbreviations shortening a strict prefix of an
    application, by Hugo Herbelin).

  - :cmd:`Numeral Notation` now support inductive types in the input to
    printing functions (e.g., numeral notations can be defined for terms
    containing things like :g:`@cons nat O O`), and parsing functions now
    fully normalize terms including parameters of constructors (so that,
    e.g., a numeral notation whose parsing function outputs a proof of
    :g:`Nat.gcd x y = 1` will no longer fail to parse due to containing the
    constant :g:`Nat.gcd` in the parameter-argument of :g:`eq_refl`)
    (`#9874 <https://github.com/coq/coq/pull/9840>`_,
    closes `#9840 <https://github.com/coq/coq/issues/9840>`_
    and `#9844 <https://github.com/coq/coq/issues/9844>`_,
    by Jason Gross).

  - Deprecated compatibility notations have actually been
    removed. Uses of these notations are generally easy to fix thanks
    to the hint contained in the deprecation warning emitted by Coq
    8.8 and 8.9.  For projects that require more than a handful of
    such fixes, there is `a script
    <https://gist.github.com/JasonGross/9770653967de3679d131c59d42de6d17#file-replace-notations-py>`_
    that will do it automatically, using the output of ``coqc``
    (`#8638 <https://github.com/coq/coq/pull/8638>`_, by Jason Gross).

  - Allow inspecting custom grammar entries by :cmd:`Print Custom Grammar`
    (`#10061 <https://github.com/coq/coq/pull/10061>`_,
    fixes `#9681 <http://github.com/coq/coq/pull/9681>`_,
    by Jasper Hugunin, review by Pierre-Marie Pédrot and Hugo Herbelin).

- The `quote plugin
  <https://coq.inria.fr/distrib/V8.9.0/refman/proof-engine/detailed-tactic-examples.html#quote>`_
  was removed. If some users are interested in maintaining this plugin
  externally, the Coq development team can provide assistance for
  extracting the plugin and setting up a new repository
  (`#7894 <https://github.com/coq/coq/pull/7894>`_, by Maxime Dénès).

- Ltac:

  - Tactic names are no longer allowed to clash, even if they are not defined in
    the same section. For example, the following is no longer accepted:
    :g:`Ltac foo := idtac. Section S. Ltac foo := fail. End S.`
    (`#8555 <https://github.com/coq/coq/pull/8555>`_, by Maxime Dénès).

  - Names of existential variables occurring in Ltac functions
    (e.g. :g:`?[n]` or :g:`?n` in terms - not in patterns) are now interpreted
    the same way as other variable names occurring in Ltac functions
    (`#7309 <https://github.com/coq/coq/pull/7309>`_, by Hugo Herbelin).

- Tactics:

  - Removed the deprecated `romega` tactic
    (`#8419 <https://github.com/coq/coq/pull/8419>`_,
    by Maxime Dénès and Vincent Laporte).

  - Hint declaration and removal should now specify a database (e.g. `Hint Resolve
    foo : database`). When the database name is omitted, the hint is added to the
    `core` database (as previously), but a deprecation warning is emitted
    (`#8987 <https://github.com/coq/coq/pull/8987>`_, by Maxime Dénès).

  - There are now tactics in `PreOmega.v` called
    `Z.div_mod_to_equations`, `Z.quot_rem_to_equations`, and
    `Z.to_euclidean_division_equations` (which combines the `div_mod`
    and `quot_rem` variants) which allow :tacn:`lia`, :tacn:`nia`, etc to
    support `Z.div` and `Z.modulo` (`Z.quot` and `Z.rem`, respectively),
    by posing the specifying equation for `Z.div` and `Z.modulo` before
    replacing them with atoms
    (`#8062 <https://github.com/coq/coq/pull/8062>`_, by Jason Gross).

  - The syntax of the :tacn:`autoapply` tactic was fixed to conform with preexisting
    documentation: it now takes a `with` clause instead of a `using` clause
    (`#9524 <https://github.com/coq/coq/pull/9524>`_,
    closes `#7632 <https://github.com/coq/coq/issues/7632>`_,
    by Théo Zimmermann).

  - Modes are now taken into account by :tacn:`typeclasses eauto` for
    local hypotheses
    (`#9996 <https://github.com/coq/coq/pull/9996>`_,
    fixes `#5752 <https://github.com/coq/coq/issues/5752>`_,
    by Maxime Dénès, review by Pierre-Marie Pédrot).

  - New variant :tacn:`change_no_check` of :tacn:`change`, usable as a
    documented replacement of :tacn:`convert_concl_no_check`
    (`#10012 <https://github.com/coq/coq/pull/10012>`_,
    `#10017 <https://github.com/coq/coq/pull/10017>`_,
    `#10053 <https://github.com/coq/coq/pull/10053>`_, and
    `#10059 <https://github.com/coq/coq/pull/10059>`_,
    by Hugo Herbelin and Paolo G. Giarrusso).

  - The simplified value returned by :tacn:`field_simplify` is not
    always a fraction anymore.  When the denominator is :g:`1`, it
    returns :g:`x` while previously it was returning :g:`x/1`.  This
    change could break codes that were post-processing application of
    :tacn:`field_simplify` to get rid of these :g:`x/1`
    (`#9854 <https://github.com/coq/coq/pull/9854>`_,
    by Laurent Théry,
    with help from Michael Soegtrop, Maxime Dénès, and Vincent Laporte).

- SSReflect:

  - Clear discipline made consistent across the entire proof language.
    Whenever a clear switch `{x..}` comes immediately before an existing proof
    context entry (used as a view, as a rewrite rule or as name for a new
    context entry) then such entry is cleared too.

    E.g. The following sentences are elaborated as follows (when H is an existing
    proof context entry):

    - `=> {x..} H`       ->  `=> {x..H} H`
    - `=> {x..} /H`      ->  `=> /v {x..H}`
    - `rewrite {x..} H`  ->  `rewrite E {x..H}`

    (`#9341 <https://github.com/coq/coq/pull/9341>`_, by Enrico Tassi).

  - `inE` now expands `y \in r x` when `r` is a `simpl_rel`.
    New `{pred T}` notation for a `pred T` alias in the `pred_sort` coercion
    class, simplified `predType` interface: `pred_class` and `mkPredType`
    deprecated, `{pred T}` and `PredType` should be used instead.
    `if c return t then ...` now expects `c` to be a variable bound in `t`.
    New `nonPropType` interface matching types that do _not_ have sort `Prop`.
    New `relpre R f` definition for the preimage of a relation R under f
    (`#9995 <https://github.com/coq/coq/pull/9995>`_, by Georges Gonthier).

- Vernacular commands:

  - Binders for an :cmd:`Instance` now act more like binders for a :cmd:`Theorem`.
    Names may not be repeated, and may not overlap with section variable names
    (`#8820 <https://github.com/coq/coq/pull/8820>`_,
    closes `#8791 <https://github.com/coq/coq/issues/8791>`_,
    by Jasper Hugunin).

  - Removed the deprecated `Implicit Tactic` family of commands
    (`#8779 <https://github.com/coq/coq/pull/8779>`_, by Pierre-Marie Pédrot).

  - The `Automatic Introduction` option has been removed and is now the
    default
    (`#9001 <https://github.com/coq/coq/pull/9001>`_,
    by Emilio Jesús Gallego Arias).

  - `Arguments` now accepts names for arguments provided with `extra_scopes`
    (`#9117 <https://github.com/coq/coq/pull/9117>`_, by Maxime Dénès).

  - The naming scheme for anonymous binders in a `Theorem` has changed to
    avoid conflicts with explicitly named binders
    (`#9160 <https://github.com/coq/coq/pull/9160>`_,
    closes `#8819 <https://github.com/coq/coq/issues/8819>`_,
    by Jasper Hugunin).

  - Computation of implicit arguments now properly handles local definitions in the
    binders for an `Instance`, and can be mixed with implicit binders `{x : T}`
    (`#9307 <https://github.com/coq/coq/pull/9307>`_,
    closes `#9300 <https://github.com/coq/coq/issues/9300>`_,
    by Jasper Hugunin).

  - :cmd:`Declare Instance` now requires an instance name.

    The flag `Refine Instance Mode` has been turned off by default, meaning that
    :cmd:`Instance` no longer opens a proof when a body is provided. The flag
    has been deprecated and will be removed in the next version.

    (`#9270 <https://github.com/coq/coq/pull/9270>`_,
    and `#9825 <https://github.com/coq/coq/pull/9825>`_,
    by Maxime Dénès)

  - Command :cmd:`Instance`, when no body is provided, now always opens
    a proof. This is a breaking change, as instance of :n:`Instance
    @ident__1 : @ident__2.` where :n:`@ident__2` is a trivial class will
    have to be changed into :n:`Instance @ident__1 : @ident__2 := %{%}.`
    or :n:`Instance @ident__1 : @ident__2. Proof. Qed.`
    (`#9274 <https://github.com/coq/coq/pull/9274>`_, by Maxime Dénès).

  - The flag :flag:`Program Mode` now means that the `Program` attribute is enabled
    for all commands that support it. In particular, it does not have any effect
    on tactics anymore. May cause some incompatibilities
    (`#9410 <https://github.com/coq/coq/pull/9410>`_, by Maxime Dénès).

  - The algorithm computing implicit arguments now behaves uniformly for primitive
    projection and application nodes
    (`#9509 <https://github.com/coq/coq/pull/9509>`_,
    closes `#9508 <https://github.com/coq/coq/issues/9508>`_,
    by Pierre-Marie Pédrot).

  - :cmd:`Hypotheses` and :cmd:`Variables` can now take implicit
    binders inside sections
    (`#9364 <https://github.com/coq/coq/pull/9364>`_,
    closes `#9363 <https://github.com/coq/coq/issues/9363>`_,
    by Jasper Hugunin).

  - Removed deprecated option `Automatic Coercions Import`
    (`#8094 <https://github.com/coq/coq/pull/8094>`_, by Maxime Dénès).

  - The ``Show Script`` command has been deprecated
    (`#9829 <https://github.com/coq/coq/pull/9829>`_, by Vincent Laporte).

  - :cmd:`Coercion` does not warn ambiguous paths which are obviously
    convertible with existing ones. The ambiguous paths messages have been
    turned to warnings, thus now they could appear in the output of ``coqc``.
    The convertibility checking procedure for coercion paths is complete for
    paths consisting of coercions satisfying the uniform inheritance condition,
    but some coercion paths could be reported as ambiguous even if they are
    convertible with existing ones when they have coercions that don't satisfy
    the uniform inheritance condition
    (`#9743 <https://github.com/coq/coq/pull/9743>`_,
    closes `#3219 <https://github.com/coq/coq/issues/3219>`_,
    by Kazuhiko Sakaguchi).

  - A new flag :flag:`Fast Name Printing` has been introduced. It changes the
    algorithm used for allocating bound variable names for a faster but less
    clever one
    (`#9078 <https://github.com/coq/coq/pull/9078>`_, by Pierre-Marie Pédrot).

  - Option ``Typeclasses Axioms Are Instances`` (compatibility option
    introduced in the previous version) is deprecated. Use :cmd:`Declare
    Instance` for axioms which should be instances
    (`#8920 <https://github.com/coq/coq/pull/8920>`_, by Gaëtan Gilbert).

  - Removed option `Printing Primitive Projection Compatibility`
    (`#9306 <https://github.com/coq/coq/pull/9306>`_, by Gaëtan Gilbert).

- Standard Library:

  - Added `Bvector.BVeq` that decides whether two `Bvector`\s are equal.
    Added notations for `BVxor`, `BVand`, `BVor`, `BVeq` and `BVneg`
    (`#8171 <https://github.com/coq/coq/pull/8171>`_, by Yishuai Li).

  - Added `ByteVector` type that can convert to and from `string`
    (`#8365 <https://github.com/coq/coq/pull/8365>`_, by Yishuai Li).

  - Added lemmas about monotonicity of `N.double` and `N.succ_double`, and about
    the upper bound of number represented by a vector.
    Allowed implicit vector length argument in `Ndigits.Bv2N`
    (`#8815 <https://github.com/coq/coq/pull/8815>`_, by Yishuai Li).

  - The prelude used to be automatically Exported and is now only
    Imported. This should be relevant only when importing files which
    don't use `-noinit` into files which do
    (`#9013 <https://github.com/coq/coq/pull/9013>`_, by Gaëtan Gilert).

  - Added `Coq.Structures.OrderedTypeEx.String_as_OT` to make strings an
    ordered type, using lexical order
    (`#7221 <https://github.com/coq/coq/pull/7221>`_, by Li Yao).

  - Added lemmas about `Z.testbit`, `Z.ones`, and `Z.modulo`
    (`#9425 <https://github.com/coq/coq/pull/9425>`_, by Andres Erbsen).

  - Moved the `auto` hints of the `FSet` library into a new
    `fset` database
    (`#9725 <https://github.com/coq/coq/pull/9725>`_, by Frédéric Besson).

  - Added :g:`Coq.Structures.EqualitiesFacts.PairUsualDecidableTypeFull`
    (`#9984 <https://github.com/coq/coq/pull/9984>`_,
    by Jean-Christophe Léchenet and Oliver Nash).

- Some error messages that show problems with a pair of non-matching
  values will now highlight the differences
  (`#8669 <https://github.com/coq/coq/pull/8669>`_, by Jim Fehrle).

- Changelog has been moved from a specific file `CHANGES.md` to the
  reference manual; former Credits chapter of the reference manual has
  been split in two parts: a History chapter which was enriched with
  additional historical information about Coq versions 1 to 5, and a
  Changes chapter which was enriched with the content formerly in
  `CHANGES.md` and `COMPATIBILITY`
  (`#9133 <https://github.com/coq/coq/pull/9133>`_,
  `#9668 <https://github.com/coq/coq/pull/9668>`_,
  `#9939 <https://github.com/coq/coq/pull/9939>`_,
  `#9964 <https://github.com/coq/coq/pull/9964>`_,
  and `#10085 <https://github.com/coq/coq/pull/10085>`_,
  by Théo Zimmermann,
  with help and ideas from Emilio Jesús Gallego Arias, Gaëtan
  Gilbert, Clément Pit-Claudel, Matthieu Sozeau, and Enrico Tassi).

Changes in 8.10+beta2
~~~~~~~~~~~~~~~~~~~~~

Many bug fixes and documentation improvements, in particular:

**Tactics**

- Make the :tacn:`discriminate` tactic work together with
  :flag:`Universe Polymorphism` and equality in :g:`Type`. This,
  in particular, makes :tacn:`discriminate` compatible with the HoTT
  library https://github.com/HoTT/HoTT
  (`#10205 <https://github.com/coq/coq/pull/10205>`_,
  by Andreas Lynge, review by Pierre-Marie Pédrot and Matthieu Sozeau).

**SSReflect**

- Make the ``case E: t`` tactic work together with
  :flag:`Universe Polymorphism` and equality in :g:`Type`.
  This makes :tacn:`case <case (ssreflect)>` compatible with the HoTT
  library https://github.com/HoTT/HoTT
  (`#10302 <https://github.com/coq/coq/pull/10302>`_,
  fixes `#10301 <https://github.com/coq/coq/issues/10301>`_,
  by Andreas Lynge, review by Enrico Tassi)
- Make the ``rewrite /t`` tactic work together with
  :flag:`Universe Polymorphism`.
  This makes :tacn:`rewrite <rewrite (ssreflect)>` compatible with the HoTT
  library https://github.com/HoTT/HoTT
  (`#10305 <https://github.com/coq/coq/pull/10305>`_,
  fixes `#9336 <https://github.com/coq/coq/issues/9336>`_,
  by Andreas Lynge, review by Enrico Tassi)

**CoqIDE**

- Fix CoqIDE instability on Windows after the update to gtk3
  (`#10360 <https://github.com/coq/coq/pull/10360>`_, by Michael Soegtrop,
  closes `#9885 <https://github.com/coq/coq/issues/9885>`_).

**Miscellaneous**

- Proof General can now display Coq-generated diffs between proof steps
  in color
  (`#10019 <https://github.com/coq/coq/pull/10019>`_ and
  (in Proof General) `#421 <https://github.com/ProofGeneral/PG/pull/421>`_,
  by Jim Fehrle).


Version 8.9
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

|Coq| version 8.9 contains the result of refinements and stabilization
of features and deprecations or removals of deprecated features,
cleanups of the internals of the system and API along with a few new
features. This release includes many user-visible changes, including
deprecations that are documented in the next subsection and new features that
are documented in the reference manual. Here are the most important
changes:

- Kernel: mutually recursive records are now supported, by Pierre-Marie
  Pédrot.

- Notations:

  - Support for autonomous grammars of terms called “custom entries”, by
    Hugo Herbelin (see Section :ref:`custom-entries` of the reference
    manual).

  - Deprecated notations of the standard library will be removed in the
    next version of |Coq|, see the next subsection for a script to
    ease porting, by Jason Gross and Jean-Christophe Léchenet.

  - Added the :cmd:`Numeral Notation` command for registering decimal
    numeral notations for custom types, by Daniel de Rauglaudre, Pierre
    Letouzey and Jason Gross.

- Tactics: Introduction tactics :tacn:`intro`/:tacn:`intros` on a goal that is an
  existential variable now force a refinement of the goal into a
  dependent product rather than failing, by Hugo Herbelin.

- Decision procedures: deprecation of tactic ``romega`` in favor of
  :tacn:`lia` and removal of ``fourier``, replaced by :tacn:`lra` which
  subsumes it, by Frédéric Besson, Maxime Dénès, Vincent Laporte and
  Laurent Théry.

- Proof language: focusing bracket ``{`` now supports named
  :ref:`goals <curly-braces>`, e.g. ``[x]:{`` will focus
  on a goal (existential variable) named ``x``, by Théo Zimmermann.

- SSReflect: the implementation of delayed clear was simplified by
  Enrico Tassi: the variables are always renamed using inaccessible
  names when the clear switch is processed and finally cleared at the
  end of the intro pattern. In addition to that, the use-and-discard flag
  ``{}`` typical of rewrite rules can now be also applied to views,
  e.g. ``=> {}/v`` applies ``v`` and then clears ``v``. See Section
  :ref:`introduction_ssr`.

- Vernacular:

  - Experimental support for :ref:`attributes <gallina-attributes>` on
    commands, by Vincent Laporte, as in ``#[local] Lemma foo : bar.``
    Tactics and tactic notations now support the ``deprecated``
    attribute.

  - Removed deprecated commands ``Arguments Scope`` and ``Implicit
    Arguments`` in favor of :cmd:`Arguments (scopes)` and
    :cmd:`Arguments (implicits)`, with the help of Jasper Hugunin.

  - New flag :flag:`Uniform Inductive Parameters` by Jasper Hugunin to
    avoid repeating uniform parameters in constructor declarations.

  - New commands :cmd:`Hint Variables` and :cmd:`Hint Constants`, by
    Matthieu Sozeau, for controlling the opacity status of variables and
    constants in hint databases. It is recommended to always use these
    commands after creating a hint database with :cmd:`Create HintDb`.

  - Multiple sections with the same name are now allowed, by Jasper
    Hugunin.

- Library: additions and changes in the ``VectorDef``, ``Ascii``, and
  ``String`` libraries. Syntax notations are now available only when using
  ``Import`` of libraries and not merely ``Require``, by various
  contributors (source of incompatibility, see the next subsection for details).

- Toplevels: ``coqtop`` and ``coqide`` can now display diffs between proof
  steps in color, using the :opt:`Diffs` option, by Jim Fehrle.

- Documentation: we integrated a large number of fixes to the new Sphinx
  documentation by various contributors, coordinated by Clément
  Pit-Claudel and Théo Zimmermann.

- Tools: removed the ``gallina`` utility and the homebrewed ``Emacs`` mode.

- Packaging: as in |Coq| 8.8.2, the Windows installer now includes many
  more external packages that can be individually selected for
  installation, by Michael Soegtrop.

Version 8.9 also comes with a bunch of smaller-scale changes and
improvements regarding the different components of the system.  Most
important ones are documented in the next subsection file.

On the implementation side, the ``dev/doc/changes.md`` file documents
the numerous changes to the implementation and improvements of
interfaces. The file provides guidelines on porting a plugin to the new
version and a plugin development tutorial kept in sync with Coq was
introduced by Yves Bertot http://github.com/ybertot/plugin_tutorials.
The new ``dev/doc/critical-bugs`` file documents the known critical bugs
of |Coq| and affected releases.

The efficiency of the whole system has seen improvements thanks to
contributions from Gaëtan Gilbert, Pierre-Marie Pédrot, and Maxime Dénès.

Maxime Dénès, Emilio Jesús Gallego Arias, Gaëtan Gilbert, Michael
Soegtrop, Théo Zimmermann worked on maintaining and improving the
continuous integration system.

The OPAM repository for |Coq| packages has been maintained by Guillaume
Melquiond, Matthieu Sozeau, Enrico Tassi with contributions from many
users. A list of packages is available at https://coq.inria.fr/opam/www/.

The 54 contributors for this version are Léo Andrès, Rin Arakaki,
Benjamin Barenblat, Langston Barrett, Siddharth Bhat, Martin Bodin,
Simon Boulier, Timothy Bourke, Joachim Breitner, Tej Chajed, Arthur
Charguéraud, Pierre Courtieu, Maxime Dénès, Andres Erbsen, Jim Fehrle,
Julien Forest, Emilio Jesus Gallego Arias, Gaëtan Gilbert, Matěj
Grabovský, Jason Gross, Samuel Gruetter, Armaël Guéneau, Hugo Herbelin,
Jasper Hugunin, Ralf Jung, Sam Pablo Kuper, Ambroise Lafont, Leonidas
Lampropoulos, Vincent Laporte, Peter LeFanu Lumsdaine, Pierre Letouzey,
Jean-Christophe Léchenet, Nick Lewycky, Yishuai Li, Sven M. Hallberg,
Assia Mahboubi, Cyprien Mangin, Guillaume Melquiond, Perry E. Metzger,
Clément Pit-Claudel, Pierre-Marie Pédrot, Daniel R. Grayson, Kazuhiko
Sakaguchi, Michael Soegtrop, Matthieu Sozeau, Paul Steckler, Enrico
Tassi, Laurent Théry, Anton Trunov, whitequark, Théo Winterhalter,
Zeimer, Beta Ziliani, Théo Zimmermann.

Many power users helped to improve the design of the new features via
the issue and pull request system, the |Coq| development mailing list or
the coq-club@inria.fr mailing list. It would be impossible to mention
exhaustively the names of everybody who to some extent influenced the
development.

Version 8.9 is the fourth release of |Coq| developed on a time-based
development cycle. Its development spanned 7 months from the release of
|Coq| 8.8. The development moved to a decentralized merging process
during this cycle. Guillaume Melquiond was in charge of the release
process and is the maintainer of this release. This release is the
result of ~2,000 commits and ~500 PRs merged, closing 75+ issues.

The |Coq| development team welcomed Vincent Laporte, a new |Coq|
engineer working with Maxime Dénès in the |Coq| consortium.

| Paris, November 2018,
| Matthieu Sozeau for the |Coq| development team
|

Details of changes in 8.9+beta1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Kernel

- Mutually defined records are now supported.

Notations

- New support for autonomous grammars of terms, called "custom
  entries" (see chapter "Syntax extensions" of the reference manual).

- Deprecated compatibility notations will actually be removed in the
  next version of Coq.  Uses of these notations are generally easy to
  fix thanks to the hint contained in the deprecation warnings. For
  projects that require more than a handful of such fixes, there is `a
  script
  <https://gist.github.com/JasonGross/9770653967de3679d131c59d42de6d17#file-replace-notations-py>`_
  that will do it automatically, using the output of ``coqc``. The script
  contains documentation on its usage in a comment at the top.

Tactics

- Added toplevel goal selector `!` which expects a single focused goal.
  Use with `Set Default Goal Selector` to force focusing before tactics
  are called.

- The undocumented "nameless" forms `fix N`, `cofix` that were
  deprecated in 8.8 have been removed from Ltac's syntax; please use
  `fix ident N/cofix ident` to explicitly name the (co)fixpoint
  hypothesis to be introduced.

- Introduction tactics `intro`/`intros` on a goal that is an
  existential variable now force a refinement of the goal into a
  dependent product rather than failing.

- Support for `fix`/`cofix` added in Ltac `match` and `lazymatch`.

- Ltac backtraces now include trace information about tactics
  called by OCaml-defined tactics.

- Option `Ltac Debug` now applies also to terms built using Ltac functions.

- Deprecated the `Implicit Tactic` family of commands.

- The default program obligation tactic uses a bounded proof search
  instead of an unbounded and potentially non-terminating one now
  (source of incompatibility).

- The `simple apply` tactic now respects the `Opaque` flag when called from
  Ltac (`auto` still does not respect it).

- Tactic `constr_eq` now adds universe constraints needed for the
  identity to the context (it used to ignore them). New tactic
  `constr_eq_strict` checks that the required constraints already hold
  without adding new ones. Preexisting tactic `constr_eq_nounivs` can
  still be used if you really want to ignore universe constraints.

- Tactics and tactic notations now understand the `deprecated` attribute.
- The `fourier` tactic has been removed. Please now use `lra` instead. You
  may need to add `Require Import Lra` to your developments. For compatibility,
  we now define `fourier` as a deprecated alias of `lra`.

- The `romega` tactics have been deprecated; please use `lia` instead.

Focusing

- Focusing bracket `{` now supports named goal selectors,
  e.g. `[x]: {` will focus on a goal (existential variable) named `x`.
  As usual, unfocus with `}` once the sub-goal is fully solved.

Specification language

- A fix to unification (which was sensitive to the ascii name of
  variables) may occasionally change type inference in incompatible
  ways, especially regarding the inference of the return clause of `match`.

Standard Library

- Added `Ascii.eqb` and `String.eqb` and the `=?` notation for them,
  and proved some lemmas about them.  Note that this might cause
  incompatibilities if you have, e.g., `string_scope` and `Z_scope` both
  open with `string_scope` on top, and expect `=?` to refer to `Z.eqb`.
  Solution: wrap `_ =? _` in `(_ =? _)%Z` (or whichever scope you
  want).

- Added `Ndigits.N2Bv_sized`, and proved some lemmas about it.
  Deprecated `Ndigits.N2Bv_gen`.

- The scopes `int_scope` and `uint_scope` have been renamed to
  `dec_int_scope` and `dec_uint_scope`, to clash less with ssreflect
  and other packages.  They are still delimited by `%int` and `%uint`.

- Syntax notations for `string`, `ascii`, `Z`, `positive`, `N`, `R`,
  and `int31` are no longer available merely by `Require`ing the files
  that define the inductives.  You must `Import` `Coq.Strings.String.StringSyntax`
  (after `Require` `Coq.Strings.String`), `Coq.Strings.Ascii.AsciiSyntax` (after
  `Require` `Coq.Strings.Ascii`), `Coq.ZArith.BinIntDef`, `Coq.PArith.BinPosDef`,
  `Coq.NArith.BinNatDef`, `Coq.Reals.Rdefinitions`, and
  `Coq.Numbers.Cyclic.Int31.Int31`, respectively, to be able to use
  these notations.  Note that passing `-compat 8.8` or issuing
  `Require Import Coq.Compat.Coq88` will make these notations
  available.  Users wishing to port their developments automatically
  may download `fix.py` from
  https://gist.github.com/JasonGross/5d4558edf8f5c2c548a3d96c17820169
  and run a command like `while true; do make -Okj 2>&1 |
  /path/to/fix.py; done` and get a cup of coffee.  (This command must
  be manually interrupted once the build finishes all the way though.
  Note also that this method is not fail-proof; you may have to adjust
  some scopes if you were relying on string notations not being
  available even when `string_scope` was open.)

- Numeral syntax for `nat` is no longer available without loading the
  entire prelude (`Require Import Coq.Init.Prelude`).  This only
  impacts users running Coq without the init library (`-nois` or
  `-noinit`) and also issuing `Require Import Coq.Init.Datatypes`.

Tools

- Coq_makefile lets one override or extend the following variables from
  the command line: `COQFLAGS`, `COQCHKFLAGS`, `COQDOCFLAGS`.
  `COQFLAGS` is now entirely separate from `COQLIBS`, so in custom Makefiles
  `$(COQFLAGS)` should be replaced by `$(COQFLAGS) $(COQLIBS)`.

- Removed the `gallina` utility (extracts specification from Coq vernacular files).
  If you would like to maintain this tool externally, please contact us.

- Removed the Emacs modes distributed with Coq. You are advised to
  use `Proof-General <https://proofgeneral.github.io/>`_ (and optionally
  `Company-Coq <https://github.com/cpitclaudel/company-coq>`_) instead.
  If your use case is not covered by these alternative Emacs modes,
  please open an issue. We can help set up external maintenance as part
  of Proof-General, or independently as part of coq-community.

Vernacular Commands

- Removed deprecated commands `Arguments Scope` and `Implicit Arguments`
  (not the option). Use the `Arguments` command instead.
- Nested proofs may be enabled through the option `Nested Proofs Allowed`.
  By default, they are disabled and produce an error. The deprecation
  warning which used to occur when using nested proofs has been removed.
- Added option `Uniform Inductive Parameters` which abstracts over parameters
  before typechecking constructors, allowing to write for example
  `Inductive list (A : Type) := nil : list | cons : A -> list -> list.`
- New `Set Hint Variables/Constants Opaque/Transparent` commands for setting
  globally the opacity flag of variables and constants in hint databases,
  overwriting the opacity set of the hint database.
- Added generic syntax for "attributes", as in:
  `#[local] Lemma foo : bar.`
- Added the `Numeral Notation` command for registering decimal numeral
  notations for custom types
- The `Set SsrHave NoTCResolution` command no longer has special global
  scope. If you want the previous behavior, use `Global Set SsrHave
  NoTCResolution`.
- Multiple sections with the same name are allowed.

Coq binaries and process model

- Before 8.9, Coq distributed a single `coqtop` binary and a set of
  dynamically loadable plugins that used to take over the main loop
  for tasks such as IDE language server or parallel proof checking.

  These plugins have been turned into full-fledged binaries so each
  different process has associated a particular binary now, in
  particular `coqidetop` is the CoqIDE language server, and
  `coq{proof,tactic,query}worker` are in charge of task-specific and
  parallel proof checking.

SSReflect

- The implementation of delayed clear switches in intro patterns
  is now simpler to explain:

  1. The immediate effect of a clear switch like `{x}` is to rename the
     variable `x` to `_x_` (i.e. a reserved identifier that cannot be mentioned
     explicitly)
  2. The delayed effect of `{x}` is that `_x_` is cleared at the end of the intro
     pattern
  3. A clear switch immediately before a view application like `{x}/v` is
     translated to `/v{x}`.

  In particular, the third rule lets one write `{x}/v` even if `v` uses the variable `x`:
  indeed the view is executed before the renaming.

- An empty clear switch is now accepted in intro patterns before a
  view application whenever the view is a variable.
  One can now write `{}/v` to mean `{v}/v`.  Remark that `{}/x` is very similar
  to the idiom `{}e` for the rewrite tactic (the equation `e` is used for
  rewriting and then discarded).

Standard Library

- There are now conversions between `string` and `positive`, `Z`,
  `nat`, and `N` in binary, octal, and hex.

Display diffs between proof steps

- `coqtop` and `coqide` can now highlight the differences between proof steps
  in color. This can be enabled from the command line or the
  `Set Diffs "on"/"off"/"removed"` command. Please see the documentation for
  details.  Showing diffs in Proof General requires small changes to PG
  (under discussion).

Notations

- Added `++` infix for `VectorDef.append`.
  Note that this might cause incompatibilities if you have, e.g., `list_scope`
  and `vector_scope` both open with `vector_scope` on top, and expect `++` to
  refer to `app`.
  Solution: wrap `_ ++ _` in `(_ ++ _)%list` (or whichever scope you want).

Changes in 8.8.0
~~~~~~~~~~~~~~~~

Various bug fixes.

Changes in 8.8.1
~~~~~~~~~~~~~~~~

- Some quality-of-life fixes.
- Numerous improvements to the documentation.
- Fix a critical bug related to primitive projections and :tacn:`native_compute`.
- Ship several additional Coq libraries with the Windows installer.

Version 8.8
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

|Coq| version 8.8 contains the result of refinements and stabilization of
features and deprecations, cleanups of the internals of the system along
with a few new features. The main user visible changes are:

- Kernel: fix a subject reduction failure due to allowing fixpoints
  on non-recursive values, by Matthieu Sozeau.
  Handling of evars in the VM (the kernel still does not accept evars)
  by Pierre-Marie Pédrot.

- Notations: many improvements on recursive notations and support for
  destructuring patterns in the syntax of notations by Hugo Herbelin.

- Proof language: tacticals for profiling, timing and checking success
  or failure of tactics by Jason Gross. The focusing bracket ``{``
  supports single-numbered goal selectors, e.g. ``2:{``, by Théo
  Zimmermann.

- Vernacular: deprecation of commands and more uniform handling of the
  ``Local`` flag, by Vincent Laporte and Maxime Dénès, part of a larger
  attribute system overhaul. Experimental ``Show Extraction`` command by
  Pierre Letouzey. Coercion now accepts ``Prop`` or ``Type`` as a source
  by Arthur Charguéraud. ``Export`` modifier for options allowing to
  export the option to modules that ``Import`` and not only ``Require``
  a module, by Pierre-Marie Pédrot.

- Universes: many user-level and API level enhancements: qualified
  naming and printing, variance annotations for cumulative inductive
  types, more general constraints and enhancements of the minimization
  heuristics, interaction with modules by Gaëtan Gilbert, Pierre-Marie
  Pédrot and Matthieu Sozeau.

- Library: Decimal Numbers library by Pierre Letouzey and various small
  improvements.

- Documentation: a large community effort resulted in the migration
  of the reference manual to the Sphinx documentation tool. The result
  is this manual. The new documentation infrastructure (based on Sphinx)
  is by Clément Pit-Claudel. The migration was coordinated by Maxime Dénès
  and Paul Steckler, with some help of Théo Zimmermann during the
  final integration phase. The 14 people who ported the manual are
  Calvin Beck, Heiko Becker, Yves Bertot, Maxime Dénès, Richard Ford,
  Pierre Letouzey, Assia Mahboubi, Clément Pit-Claudel,
  Laurence Rideau, Matthieu Sozeau, Paul Steckler, Enrico Tassi,
  Laurent Théry, Nikita Zyuzin.

- Tools: experimental ``-mangle-names`` option to ``coqtop``/``coqc`` for
  linting proof scripts, by Jasper Hugunin.

On the implementation side, the ``dev/doc/changes.md`` file
documents the numerous changes to the implementation and improvements of
interfaces. The file provides guidelines on porting a plugin to the new
version.

Version 8.8 also comes with a bunch of smaller-scale changes and
improvements regarding the different components of the system.
Most important ones are documented in the next subsection file.

The efficiency of the whole system has seen improvements thanks to
contributions from Gaëtan Gilbert, Pierre-Marie Pédrot, Maxime Dénès and
Matthieu Sozeau and performance issue tracking by Jason Gross and Paul
Steckler.

The official wiki and the bugtracker of |Coq| migrated to the GitHub
platform, thanks to the work of Pierre Letouzey and Théo
Zimmermann. Gaëtan Gilbert, Emilio Jesús Gallego Arias worked on
maintaining and improving the continuous integration system.

The OPAM repository for |Coq| packages has been maintained by Guillaume
Melquiond, Matthieu Sozeau, Enrico Tassi with contributions from many
users. A list of packages is available at https://coq.inria.fr/opam/www/.

The 44 contributors for this version are Yves Bertot, Joachim Breitner, Tej
Chajed, Arthur Charguéraud, Jacques-Pascal Deplaix, Maxime Dénès, Jim Fehrle,
Julien Forest, Yannick Forster, Gaëtan Gilbert, Jason Gross, Samuel Gruetter,
Thomas Hebb, Hugo Herbelin, Jasper Hugunin, Emilio Jesus Gallego Arias, Ralf
Jung, Johannes Kloos, Matej Košík, Robbert Krebbers, Tony Beta Lambda, Vincent
Laporte, Peter LeFanu Lumsdaine, Pierre Letouzey, Farzon Lotfi, Cyprien Mangin,
Guillaume Melquiond, Raphaël Monat, Carl Patenaude Poulin, Pierre-Marie Pédrot,
Clément Pit-Claudel, Matthew Ryan, Matt Quinn, Sigurd Schneider, Bernhard
Schommer, Michael Soegtrop, Matthieu Sozeau, Arnaud Spiwack, Paul Steckler,
Enrico Tassi, Anton Trunov, Martin Vassor, Vadim Zaliva and Théo Zimmermann.

Version 8.8 is the third release of |Coq| developed on a time-based
development cycle. Its development spanned 6 months from the release of
|Coq| 8.7 and was based on a public roadmap. The development process
was coordinated by Matthieu Sozeau. Maxime Dénès was in charge of the
release process. Théo Zimmermann is the maintainer of this release.

Many power users helped to improve the design of the new features via
the bug tracker, the pull request system, the |Coq| development mailing
list or the coq-club@inria.fr mailing list. Special thanks to the users who
contributed patches and intensive brain-storming and code reviews,
starting with Jason Gross, Ralf Jung, Robbert Krebbers and Amin Timany.
It would however be impossible to mention exhaustively the names
of everybody who to some extent influenced the development.

The |Coq| consortium, an organization directed towards users and
supporters of the system, is now running and employs Maxime Dénès.
The contacts of the Coq Consortium are Yves Bertot and Maxime Dénès.

| Santiago de Chile, March 2018,
| Matthieu Sozeau for the |Coq| development team
|

Details of changes in 8.8+beta1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Kernel

- Support for template polymorphism for definitions was removed. May trigger
  more "universe inconsistency" errors in rare occasions.
- Fixpoints are no longer allowed on non-recursive inductive types.

Notations

- Recursive notations with the recursive pattern repeating on the
  right (e.g. "( x ; .. ; y ; z )") now supported.
- Notations with a specific level for the leftmost nonterminal,
  when printing-only, are supported.
- Notations can now refer to the syntactic category of patterns (as in
  "fun 'pat =>" or "match p with pat => ... end"). Two variants are
  available, depending on whether a single variable is considered as a
  pattern or not.
- Recursive notations now support ".." patterns with several
  occurrences of the recursive term or binder, possibly mixing terms
  and binders, possibly in reverse left-to-right order.
- "Locate" now working also on notations of the form "x + y" (rather
  than "_ + _").

Specification language

- When printing clauses of a "match", clauses with same right-hand
  side are factorized and the last most factorized clause with no
  variables, if it exists, is turned into a default clause.
  Use "Unset Printing Allow Default Clause" do deactivate printing
  of a default clause.
  Use "Unset Printing Factorizable Match Patterns" to deactivate
  factorization of clauses with same right-hand side.

Tactics

- On Linux, "native_compute" calls can be profiled using the "perf"
  utility. The command "Set NativeCompute Profiling" enables
  profiling, and "Set NativeCompute Profile Filename" customizes
  the profile filename.
- The tactic "omega" is now aware of the bodies of context variables
  such as "x := 5 : Z" (see #1362). This could be disabled via
  Unset Omega UseLocalDefs.
- The tactic "romega" is also aware now of the bodies of context variables.
- The tactic "zify" resp. "omega with N" is now aware of N.pred.
- Tactic "decide equality" now able to manage constructors which
  contain proofs.
- Added tactics reset ltac profile, show ltac profile (and variants)
- Added tactics restart_timer, finish_timing, and time_constr as an
  experimental way of timing Ltac's evaluation phase
- Added tactic optimize_heap, analogous to the Vernacular Optimize
  Heap, which performs a major garbage collection and heap compaction
  in the OCaml run-time system.
- The tactics "dtauto", "dintuition", "firstorder" now handle inductive types
  with let bindings in the parameters.
- The tactic ``dtauto`` now handles some inductives such as
  ``@sigT A (fun _ => B)`` as non-dependent conjunctions.
- A bug fixed in ``rewrite H in *`` and ``rewrite H in * |-`` may cause a
  few rare incompatibilities (it was unintendedly recursively
  rewriting in the side conditions generated by H).
- Added tactics "assert_succeeds tac" and "assert_fails tac" to ensure
  properties of the execution of a tactic without keeping the effect
  of the execution.
- `vm_compute` now supports existential variables.
- Calls to `shelve` and `give_up` within calls to tactic `refine` now working.
- Deprecated tactic `appcontext` was removed.

Focusing

- Focusing bracket `{` now supports single-numbered goal selector,
  e.g. `2: {` will focus on the second sub-goal. As usual, unfocus
  with `}` once the sub-goal is fully solved.
  The `Focus` and `Unfocus` commands are now deprecated.

Vernacular Commands

- Proofs ending in "Qed exporting ident, .., ident" are not supported
  anymore. Constants generated during `abstract` are kept private to the
  local environment.
- The deprecated Coercion Local, Open Local Scope, Notation Local syntax
  was removed. Use Local as a prefix instead.
- For the Extraction Language command, "OCaml" is spelled correctly.
  The older "Ocaml" is still accepted, but deprecated.
- Using “Require” inside a section is deprecated.
- An experimental command "Show Extraction" allows to extract the content
  of the current ongoing proof (grant wish #4129).
- Coercion now accepts the type of its argument to be "Prop" or "Type".
- The "Export" modifier can now be used when setting and unsetting options, and
  will result in performing the same change when the module corresponding the
  command is imported.
- The `Axiom` command does not automatically declare axioms as instances when
  their type is a class. Previous behavior can be restored using `Set
  Typeclasses Axioms Are Instances`.

Universes

- Qualified naming of global universes now works like other namespaced
  objects (e.g. constants), with a separate namespace, inside and across
  module and library boundaries. Global universe names introduced in an
  inductive / constant / Let declaration get qualified with the name of
  the declaration.
- Universe cumulativity for inductive types is now specified as a
  variance for each polymorphic universe. See the reference manual for
  more information.
- Inference of universe constraints with cumulative inductive types
  produces more general constraints. Unsetting new option Cumulativity
  Weak Constraints produces even more general constraints (but may
  produce too many universes to be practical).
- Fix #5726: Notations that start with `Type` now support universe instances
  with `@{u}`.
- `with Definition` now understands universe declarations
  (like `@{u| Set < u}`).

Tools

- Coq can now be run with the option -mangle-names to change the auto-generated
  name scheme. This is intended to function as a linter for developments that
  want to be robust to changes in auto-generated names. This feature is experimental,
  and may change or disappear without warning.
- GeoProof support was removed.

Checker

- The checker now accepts filenames in addition to logical paths.

CoqIDE

- Find and Replace All report the number of occurrences found; Find indicates
  when it wraps.

coqdep

- Learned to read -I, -Q, -R and filenames from _CoqProject files.
  This is used by coq_makefile when generating dependencies for .v
  files (but not other files).

Documentation

- The Coq FAQ, formerly located at https://coq.inria.fr/faq, has been
  moved to the GitHub wiki section of this repository; the main entry
  page is https://github.com/coq/coq/wiki/The-Coq-FAQ.
- Documentation: a large community effort resulted in the migration
  of the reference manual to the Sphinx documentation tool. The result
  is partially integrated in this version.

Standard Library

- New libraries Coq.Init.Decimal, Coq.Numbers.DecimalFacts,
  Coq.Numbers.DecimalNat, Coq.Numbers.DecimalPos,
  Coq.Numbers.DecimalN, Coq.Numbers.DecimalZ,
  Coq.Numbers.DecimalString providing a type of decimal numbers, some
  facts about them, and conversions between decimal numbers and nat,
  positive, N, Z, and string.
- Added [Coq.Strings.String.concat] to concatenate a list of strings
  inserting a separator between each item
- Notation `'` for Zpos in QArith was removed.

- Some deprecated aliases are now emitting warnings when used.

Compatibility support

- Support for compatibility with versions before 8.6 was dropped.

Options

- The following deprecated options have been removed:

  + `Refolding Reduction`
  + `Standard Proposition Elimination`
  + `Dependent Propositions Elimination`
  + `Discriminate Introduction`
  + `Shrink Abstract`
  + `Tactic Pattern Unification`
  + `Intuition Iff Unfolding`
  + `Injection L2R Pattern Order`
  + `Record Elimination Schemes`
  + `Match Strict`
  + `Tactic Compat Context`
  + `Typeclasses Legacy Resolution`
  + `Typeclasses Module Eta`
  + `Typeclass Resolution After Apply`

Details of changes in 8.8.0
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tools

- Asynchronous proof delegation policy was fixed. Since version 8.7
  Coq was ignoring previous runs and the `-async-proofs-delegation-threshold`
  option did not have the expected behavior.

Tactic language

- The undocumented "nameless" forms `fix N`, `cofix` have been
  deprecated; please use `fix ident N /cofix ident` to explicitly
  name the (co)fixpoint hypothesis to be introduced.

Documentation

- The reference manual is now fully ported to Sphinx.

Other small deprecations and bug fixes.

Details of changes in 8.8.1
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Kernel

- Fix a critical bug with cofixpoints and `vm_compute`/`native_compute` (#7333).
- Fix a critical bug with modules and algebraic universes (#7695)
- Fix a critical bug with inlining of polymorphic constants (#7615).
- Fix a critical bug with universe polymorphism and `vm_compute` (#7723). Was
  present since 8.5.

Notations

- Fixed unexpected collision between only-parsing and only-printing
  notations (issue #7462).

Windows installer

- The Windows installer now includes external packages Ltac2 and Equations
  (it included the Bignums package since 8.8+beta1).

Many other bug fixes, documentation improvements (including fixes of
regressions due to the Sphinx migration), and user message improvements
(for details, see the 8.8.1 milestone at
https://github.com/coq/coq/milestone/13?closed=1).

Details of changes in 8.8.2
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Documentation

- A PDF version of the reference manual is available once again.

Tools

- The coq-makefile targets `print-pretty-timed`, `print-pretty-timed-diff`,
  and `print-pretty-single-time-diff` now correctly label the "before" and
  "after" columns, rather than swapping them.

Kernel

- The kernel does not tolerate capture of global universes by
  polymorphic universe binders, fixing a soundness break (triggered
  only through custom plugins)

Windows installer

- The Windows installer now includes many more external packages that can be
  individually selected for installation.

Many other bug fixes and lots of documentation improvements (for details,
see the 8.8.2 milestone at https://github.com/coq/coq/milestone/15?closed=1).

Version 8.7
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

|Coq| version 8.7 contains the result of refinements, stabilization of features
and cleanups of the internals of the system along with a few new features. The
main user visible changes are:

- New tactics: variants of tactics supporting existential variables :tacn:`eassert`,
  :tacn:`eenough`, etc... by Hugo Herbelin. Tactics ``extensionality in H`` and
  :tacn:`inversion_sigma` by Jason Gross, ``specialize with ...`` accepting partial bindings
  by Pierre Courtieu.

- ``Cumulative Polymorphic Inductive`` types, allowing cumulativity of universes to
  go through applied inductive types, by Amin Timany and Matthieu Sozeau.

- Integration of the SSReflect plugin and its documentation in the reference
  manual, by Enrico Tassi, Assia Mahboubi and Maxime Dénès.

- The ``coq_makefile`` tool was completely redesigned to improve its maintainability
  and the extensibility of generated Makefiles, and to make ``_CoqProject`` files
  more palatable to IDEs by Enrico Tassi.

|Coq| 8.7 involved a large amount of work on cleaning and speeding up the code
base, notably the work of Pierre-Marie Pédrot on making the tactic-level system
insensitive to existential variable expansion, providing a safer API to plugin
writers and making the code more robust. The ``dev/doc/changes.txt`` file
documents the numerous changes to the implementation and improvements of
interfaces. An effort to provide an official, streamlined API to plugin writers
is in progress, thanks to the work of Matej Košík.

Version 8.7 also comes with a bunch of smaller-scale changes and improvements
regarding the different components of the system. We shall only list a few of
them.

The efficiency of the whole system has been significantly improved thanks to
contributions from Pierre-Marie Pédrot, Maxime Dénès and Matthieu Sozeau and
performance issue tracking by Jason Gross and Paul Steckler.

Thomas Sibut-Pinote and Hugo Herbelin added support for side effect hooks in
cbv, cbn and simpl. The side effects are provided via a plugin available at
https://github.com/herbelin/reduction-effects/.

The BigN, BigZ, BigQ libraries are no longer part of the |Coq| standard library,
they are now provided by a separate repository https://github.com/coq/bignums,
maintained by Pierre Letouzey.

In the Reals library, ``IZR`` has been changed to produce a compact representation
of integers and real constants are now represented using ``IZR`` (work by
Guillaume Melquiond).

Standard library additions and improvements by Jason Gross, Pierre Letouzey and
others, documented in the next subsection file.

The mathematical proof language/declarative mode plugin was removed from the
archive.

The OPAM repository for |Coq| packages has been maintained by Guillaume Melquiond,
Matthieu Sozeau, Enrico Tassi with contributions from many users. A list of
packages is available at https://coq.inria.fr/opam/www/.

Packaging tools and software development kits were prepared by Michael Soegtrop
with the help of Maxime Dénès and Enrico Tassi for Windows, and Maxime Dénès for
MacOS X. Packages are regularly built on the Travis continuous integration
server.

The contributors for this version are Abhishek Anand, C.J. Bell, Yves Bertot,
Frédéric Besson, Tej Chajed, Pierre Courtieu, Maxime Dénès, Julien Forest,
Gaëtan Gilbert, Jason Gross, Hugo Herbelin, Emilio Jesús Gallego Arias, Ralf
Jung, Matej Košík, Xavier Leroy, Pierre Letouzey, Assia Mahboubi, Cyprien
Mangin, Erik Martin-Dorel, Olivier Marty, Guillaume Melquiond, Sam Pablo Kuper,
Benjamin Pierce, Pierre-Marie Pédrot, Lars Rasmusson, Lionel Rieg, Valentin
Robert, Yann Régis-Gianas, Thomas Sibut-Pinote, Michael Soegtrop, Matthieu
Sozeau, Arnaud Spiwack, Paul Steckler, George Stelle, Pierre-Yves Strub, Enrico
Tassi, Hendrik Tews, Amin Timany, Laurent Théry, Vadim Zaliva and Théo
Zimmermann.

The development process was coordinated by Matthieu Sozeau with the help of
Maxime Dénès, who was also in charge of the release process. Théo Zimmermann is
the maintainer of this release.

Many power users helped to improve the design of the new features via the bug
tracker, the pull request system, the |Coq| development mailing list or the
Coq-Club mailing list. Special thanks to the users who contributed patches and
intensive brain-storming and code reviews, starting with Jason Gross, Ralf Jung,
Robbert Krebbers, Xavier Leroy, Clément Pit–Claudel and Gabriel Scherer. It
would however be impossible to mention exhaustively the names of everybody who
to some extent influenced the development.

Version 8.7 is the second release of |Coq| developed on a time-based development
cycle. Its development spanned 9 months from the release of |Coq| 8.6 and was
based on a public road-map. It attracted many external contributions. Code
reviews and continuous integration testing were systematically used before
integration of new features, with an important focus given to compatibility and
performance issues, resulting in a hopefully more robust release than |Coq| 8.6
while maintaining compatibility.

|Coq| Enhancement Proposals (CEPs for short) and open pull request discussions
were used to discuss publicly the new features.

The |Coq| consortium, an organization directed towards users and supporters of the
system, is now upcoming and will rely on Inria’s newly created Foundation.

| Paris, August 2017,
| Matthieu Sozeau and the |Coq| development team
|

Potential compatibility issues
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- Extra superfluous names in introduction patterns may now raise an
  error rather than a warning when the superfluous name is already in
  use. The easy fix is to remove the superfluous name.

Details of changes in 8.7+beta1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tactics

- New tactic "extensionality in H" which applies (possibly dependent)
  functional extensionality in H supposed to be a quantified equality
  until giving a bare equality.

- New tactic ``inversion_sigma`` which turns equalities of dependent
  pairs (e.g., ``existT P x p = existT P y q``, frequently left over by
  ``inversion`` on a dependent type family) into pairs of equalities
  (e.g., a hypothesis ``H : x = y`` and a hypothesis of type ``rew H in p = q``);
  these hypotheses can subsequently be simplified using
  ``subst``, without ever invoking any kind of axiom asserting
  uniqueness of identity proofs. If you want to explicitly specify the
  hypothesis to be inverted, or name the generated hypotheses, you can
  invoke ``induction H as [H1 H2] using eq_sigT_rect``.  The tactic also
  works for ``sig``, ``sigT2``, and ``sig2``, and there are similar
  ``eq_sig*_rect`` induction lemmas.

- Tactic "specialize with ..." now accepts any partial bindings.
  Missing bindings are either solved by unification or left quantified
  in the hypothesis.

- New representation of terms that statically ensure stability by
  evar-expansion. This has several consequences.

  * In terms of performance, this adds a cost to every term destructuration,
    but at the same time most eager evar normalizations were removed, which
    couterbalances this drawback and even sometimes outperforms the old
    implementation. For instance, many operations that would require O(n)
    normalization of the term are now O(1) in tactics. YMMV.

  * This triggers small changes in unification, which was not evar-insensitive.
    Most notably, the new implementation recognizes Miller patterns that were
    missed before because of a missing normalization step. Hopefully this should
    be fairly uncommon.

- Tactic "auto with real" can now discharge comparisons of literals.

- The types of variables in patterns of "match" are now
  beta-iota-reduced after type-checking. This has an impact on the
  type of the variables that the tactic "refine" introduces in the
  context, producing types a priori closer to the expectations.

- In "Tactic Notation" or "TACTIC EXTEND", entry "constr_with_bindings"
  now uses type classes and rejects terms with unresolved holes, like
  entry "constr" does. To get the former behavior use
  "open_constr_with_bindings" (possible source of incompatibility).

- New e-variants eassert, eenough, epose proof, eset, eremember, epose
  which behave like the corresponding variants with no "e" but turn
  unresolved implicit arguments into existential variables, on the
  shelf, rather than failing.

- Tactic injection has become more powerful (closes bug #4890) and its
  documentation has been updated.

- New variants of the `first` and `solve` tacticals that do not rely
  on parsing rules, meant to define tactic notations.

- Added support for side effects hooks in `cbv`, `cbn` and `simpl`.
  The side effects are provided via a plugin:
  https://github.com/herbelin/reduction-effects/

- It is now possible to take hint database names as parameters in a
  Ltac definition or a Tactic Notation.

- New option `Set Ltac Batch Debug` on top of `Set Ltac Debug` for
  non-interactive Ltac debug output.

Gallina

- Now supporting all kinds of binders, including 'pat, in syntax of record fields.

Vernacular Commands

- Goals context can be printed in a more compact way when `Set
  Printing Compact Contexts` is activated.
- Unfocused goals can be printed with the `Set Printing Unfocused`
  option.
- `Print` now shows the types of let-bindings.
- The compatibility options for printing primitive projections
  (`Set Printing Primitive Projection Parameters` and
  `Set Printing Primitive Projection Compatibility`) are now off by default.
- Possibility to unset the printing of notations in a more fine grained
  fashion than `Unset Printing Notations` is provided without any
  user-syntax. The goal is that someone creates a plugin to experiment
  such a user-syntax, to be later integrated in Coq when stabilized.
- `About` now tells if a reference is a coercion.
- The deprecated `Save` vernacular and its form `Save Theorem id` to
  close proofs have been removed from the syntax. Please use `Qed`.
- `Search` now sorts results by relevance (the relevance metric is a
  weighted sum of number of distinct symbols and size of the term).

Standard Library

- New file PropExtensionality.v to explicitly work in the axiomatic
  context of propositional extensionality.
- New file SetoidChoice.v axiomatically providing choice over setoids,
  and, consequently, choice of representatives in equivalence classes.
  Various proof-theoretic characterizations of choice over setoids in
  file ChoiceFacts.v.
- New lemmas about iff and about orders on positive and Z.
- New lemmas on powerRZ.
- Strengthened statement of JMeq_eq_dep (closes bug #4912).
- The BigN, BigZ, BigZ libraries are no longer part of the Coq standard
  library, they are now provided by a separate repository
  https://github.com/coq/bignums
  The split has been done just after the Int31 library.

- IZR (Reals) has been changed to produce a compact representation of
  integers. As a consequence, IZR is no longer convertible to INR and
  lemmas such as INR_IZR_INZ should be used instead.
- Real constants are now represented using IZR rather than R0 and R1;
  this might cause rewriting rules to fail to apply to constants.
- Added new notation {x & P} for sigT (without a type for x)

Plugins

- The Ssreflect plugin is now distributed with Coq. Its documentation has
  been integrated as a chapter of the reference manual. This chapter is
  work in progress so feedback is welcome.
- The mathematical proof language (also known as declarative mode) was removed.
- A new command Extraction TestCompile has been introduced, not meant
  for the general user but instead for Coq's test-suite.
- The extraction plugin is no longer loaded by default. It must be
  explicitly loaded with [Require Extraction], which is backwards
  compatible.
- The functional induction plugin (which provides the [Function]
  vernacular) is no longer loaded by default. It must be explicitly
  loaded with [Require FunInd], which is backwards compatible.


Dependencies

- Support for camlp4 has been removed.

Tools

- coq_makefile was completely redesigned to improve its maintainability and
  the extensibility of generated Makefiles, and to make _CoqProject files
  more palatable to IDEs.  Overview:

  * _CoqProject files contain only Coq specific data (i.e. the list of
    files, -R options, ...)
  * coq_makefile translates _CoqProject to Makefile.conf and copies in the
    desired location a standard Makefile (that reads Makefile.conf)
  * Makefile extensions can be implemented in a Makefile.local file (read
    by the main Makefile) by installing a hook in the extension points
    provided by the standard Makefile

  The current version contains code for retro compatibility that prints
  warnings when a deprecated feature is used.  Please upgrade your _CoqProject
  accordingly.

  * Additionally, coq_makefile-made Makefiles now support experimental timing
    targets `pretty-timed`, `pretty-timed-before`, `pretty-timed-after`,
    `print-pretty-timed-diff`, `print-pretty-single-time-diff`,
    `all.timing.diff`, and the variable `TIMING=1` (or `TIMING=before` or
    `TIMING=after`); see the documentation for more details.

Build Infrastructure

- Note that 'make world' does not build the bytecode binaries anymore.
  For that, you can use 'make byte' (and 'make install-byte' afterwards).
  Warning: native and byte compilations should *not* be mixed in the same
  instance of 'make -j', otherwise both ocamlc and ocamlopt might race for
  access to the same .cmi files. In short, use "make -j && make -j byte"
  instead of "make -j world byte".

Universes

- Cumulative inductive types. see prefixes "Cumulative", "NonCumulative"
  for inductive definitions and the option "Set Polymorphic Inductive Cumulativity"
  in the reference manual.
- New syntax `foo@{_}` to instantiate a polymorphic definition with
  anonymous universes (can also be used with `Type`).

XML Protocol and internal changes

See dev/doc/changes.txt

Many bugfixes including #1859, #2884, #3613, #3943, #3994,
#4250, #4709, #4720, #4824, #4844, #4911, #5026, #5233,
#5275, #5315, #5336, #5360, #5390, #5414, #5417, #5420,
#5439, #5449, #5475, #5476, #5482, #5501, #5507, #5520,
#5523, #5524, #5553, #5577, #5578, #5589, #5597, #5598,
#5607, #5618, #5619, #5620, #5641, #5648, #5651, #5671.

Many bugfixes on OS X and Windows (now the test-suite passes on these
platforms too).

Many optimizations.

Many documentation improvements.

Details of changes in 8.7+beta2
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tools

- In CoqIDE, the "Compile Buffer" command takes account of flags in
  _CoqProject or other project file.

Improvements around some error messages.

Many bug fixes including two important ones:

- Bug #5730: CoqIDE becomes unresponsive on file open.
- coq_makefile: make sure compile flags for Coq and coq_makefile are in sync
  (in particular, make sure the `-safe-string` option is used to compile plugins).

Details of changes in 8.7.0
~~~~~~~~~~~~~~~~~~~~~~~~~~~

OCaml

- Users can pass specific flags to the OCaml optimizing compiler by
  -using the flambda-opts configure-time option.

  Beware that compiling Coq with a flambda-enabled compiler is
  experimental and may require large amounts of RAM and CPU, see
  INSTALL for more details.

Details of changes in 8.7.1
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Compatibility with OCaml 4.06.0.

Many bug fixes, documentation improvements, and user message improvements (for
details see the 8.7.1 milestone at https://github.com/coq/coq/milestone/10?closed=1).

Details of changes in 8.7.2
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Fixed a critical bug in the VM handling of universes (#6677). This bug
affected all releases since 8.5.

Improved support for building with OCaml 4.06.0 and external num package.

Many other bug fixes, documentation improvements, and user
message improvements (for details, see the 8.7.2 milestone at
https://github.com/coq/coq/milestone/11?closed=1).

Version 8.6
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

Coq version 8.6 contains the result of refinements, stabilization of
8.5’s features and cleanups of the internals of the system. Over the
year of (now time-based) development, about 450 bugs were resolved and
over 100 contributions integrated. The main user visible changes are:

-  A new, faster state-of-the-art universe constraint checker, by
   Jacques-Henri Jourdan.

-  In |CoqIDE| and other asynchronous interfaces, more fine-grained
   asynchronous processing and error reporting by Enrico Tassi, making
   |Coq| capable of recovering from errors and continue processing the
   document.

-  More access to the proof engine features from Ltac: goal management
   primitives, range selectors and a :tacn:`typeclasses eauto` engine handling
   multiple goals and multiple successes, by Cyprien Mangin, Matthieu
   Sozeau and Arnaud Spiwack.

-  Tactic behavior uniformization and specification, generalization of
   intro-patterns by Hugo Herbelin and others.

-  A brand new warning system allowing to control warnings, turn them
   into errors or ignore them selectively by Maxime Dénès, Guillaume
   Melquiond, Pierre-Marie Pédrot and others.

-  Irrefutable patterns in abstractions, by Daniel de Rauglaudre.

-  The ssreflect subterm selection algorithm by Georges Gonthier and
   Enrico Tassi is now accessible to tactic writers through the
   ssrmatching plugin.

-  Integration of LtacProf, a profiler for Ltac by Jason Gross, Paul
   Steckler, Enrico Tassi and Tobias Tebbi.

Coq 8.6 also comes with a bunch of smaller-scale changes and
improvements regarding the different components of the system. We shall
only list a few of them.

The iota reduction flag is now a shorthand for match, fix and cofix
flags controlling the corresponding reduction rules (by Hugo Herbelin
and Maxime Dénès).

Maxime Dénès maintained the native compilation machinery.

Pierre-Marie Pédrot separated the Ltac code from general purpose
tactics, and generalized and rationalized the handling of generic
arguments, allowing to create new versions of Ltac more easily in the
future.

In patterns and terms, @, abbreviations and notations are now
interpreted the same way, by Hugo Herbelin.

Name handling for universes has been improved by Pierre-Marie Pédrot and
Matthieu Sozeau. The minimization algorithm has been improved by
Matthieu Sozeau.

The unifier has been improved by Hugo Herbelin and Matthieu Sozeau,
fixing some incompatibilities introduced in |Coq| 8.5. Unification
constraints can now be left floating around and be seen by the user
thanks to a new option. The Keyed Unification mode has been improved by
Matthieu Sozeau.

The typeclass resolution engine and associated proof-search tactic have
been reimplemented on top of the proof-engine monad, providing better
integration in tactics, and new options have been introduced to control
it, by Matthieu Sozeau with help from Théo Zimmermann.

The efficiency of the whole system has been significantly improved
thanks to contributions from Pierre-Marie Pédrot, Maxime Dénès and
Matthieu Sozeau and performance issue tracking by Jason Gross and Paul
Steckler.

Standard library improvements by Jason Gross, Sébastien Hinderer, Pierre
Letouzey and others.

Emilio Jesús Gallego Arias contributed many cleanups and refactorings of
the pretty-printing and user interface communication components.

Frédéric Besson maintained the micromega tactic.

The OPAM repository for |Coq| packages has been maintained by Guillaume
Claret, Guillaume Melquiond, Matthieu Sozeau, Enrico Tassi and others. A
list of packages is now available at https://coq.inria.fr/opam/www/.

Packaging tools and software development kits were prepared by Michael
Soegtrop with the help of Maxime Dénès and Enrico Tassi for Windows, and
Maxime Dénès and Matthieu Sozeau for MacOS X. Packages are now regularly
built on the continuous integration server. |Coq| now comes with a META
file usable with ocamlfind, contributed by Emilio Jesús Gallego Arias,
Gregory Malecha, and Matthieu Sozeau.

Matej Košík maintained and greatly improved the continuous integration
setup and the testing of |Coq| contributions. He also contributed many API
improvements and code cleanups throughout the system.

The contributors for this version are Bruno Barras, C.J. Bell, Yves
Bertot, Frédéric Besson, Pierre Boutillier, Tej Chajed, Guillaume
Claret, Xavier Clerc, Pierre Corbineau, Pierre Courtieu, Maxime Dénès,
Ricky Elrod, Emilio Jesús Gallego Arias, Jason Gross, Hugo Herbelin,
Sébastien Hinderer, Jacques-Henri Jourdan, Matej Košík, Xavier Leroy,
Pierre Letouzey, Gregory Malecha, Cyprien Mangin, Erik Martin-Dorel,
Guillaume Melquiond, Clément Pit–Claudel, Pierre-Marie Pédrot, Daniel de
Rauglaudre, Lionel Rieg, Gabriel Scherer, Thomas Sibut-Pinote, Matthieu
Sozeau, Arnaud Spiwack, Paul Steckler, Enrico Tassi, Laurent Théry,
Nickolai Zeldovich and Théo Zimmermann. The development process was
coordinated by Hugo Herbelin and Matthieu Sozeau with the help of Maxime
Dénès, who was also in charge of the release process.

Many power users helped to improve the design of the new features via
the bug tracker, the pull request system, the |Coq| development mailing
list or the Coq-Club mailing list. Special thanks to the users who
contributed patches and intensive brain-storming and code reviews,
starting with Cyril Cohen, Jason Gross, Robbert Krebbers, Jonathan
Leivent, Xavier Leroy, Gregory Malecha, Clément Pit–Claudel, Gabriel
Scherer and Beta Ziliani. It would however be impossible to mention
exhaustively the names of everybody who to some extent influenced the
development.

Version 8.6 is the first release of |Coq| developed on a time-based
development cycle. Its development spanned 10 months from the release of
Coq 8.5 and was based on a public roadmap. To date, it contains more
external contributions than any previous |Coq| system. Code reviews were
systematically done before integration of new features, with an
important focus given to compatibility and performance issues, resulting
in a hopefully more robust release than |Coq| 8.5.

Coq Enhancement Proposals (CEPs for short) were introduced by Enrico
Tassi to provide more visibility and a discussion period on new
features, they are publicly available https://github.com/coq/ceps.

Started during this period, an effort is led by Yves Bertot and Maxime
Dénès to put together a |Coq| consortium.

| Paris, November 2016,
| Matthieu Sozeau and the |Coq| development team
|

Potential sources of incompatibilities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- Symptom: An obligation generated by Program or an abstracted subproof
  has different arguments.

  Cause: Set Shrink Abstract and Set Shrink Obligations are on by default
  and the subproof does not use the argument.

  Remedy:

  + Adapt the script.
  + Write an explicit lemma to prove the obligation/subproof and use it
    instead (compatible with 8.4).
  + Unset the option for the program/proof the obligation/subproof originates
    from.

- Symptom: In a goal, order of hypotheses, or absence of an equality of
  the form "x = t" or "t = x", or no unfolding of a local definition.

  Cause: This might be connected to a number of fixes in the tactic
  "subst". The former behavior can be reactivated by issuing "Unset
  Regular Subst Tactic".

Details of changes in 8.6beta1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Kernel

- A new, faster state-of-the-art universe constraint checker.

Specification language

- Giving implicit arguments explicitly to a constant with multiple
  choices of implicit arguments does not break any more insertion of
  further maximal implicit arguments.
- Ability to put any pattern in binders, prefixed by quote, e.g.
  "fun '(a,b) => ...", "λ '(a,(b,c)), ...", "Definition foo '(x,y) := ...".
  It expands into a "let 'pattern := ..."

Tactics

- Flag "Bracketing Last Introduction Pattern" is now on by default.
- Flag "Regular Subst Tactic" is now on by default: it respects the
  initial order of hypothesis, it contracts cycles, it unfolds no
  local definitions (common source of incompatibilities, fixable by
  "Unset Regular Subst Tactic").
- New flag "Refolding Reduction", now disabled by default, which turns
  on refolding of constants/fixpoints (as in cbn) during the reductions
  done during type inference and tactic retyping. Can be extremely
  expensive. When set off, this recovers the 8.4 behaviour of unification
  and type inference. Potential source of incompatibility with 8.5 developments
  (the option is set on in Compat/Coq85.v).
- New flag "Shrink Abstract" that minimalizes proofs generated by the abstract
  tactical w.r.t. variables appearing in the body of the proof.
  On by default and deprecated. Minor source of incompatibility
  for code relying on the precise arguments of abstracted proofs.
- Serious bugs are fixed in tactic "double induction" (source of
  incompatibilities as soon as the inductive types have dependencies in
  the type of their constructors; "double induction" remains however
  deprecated).
- In introduction patterns of the form (pat1,...,patn), n should match
  the exact number of hypotheses introduced (except for local definitions
  for which pattern can be omitted, as in regular pattern-matching).
- Tactic scopes in Ltac like constr: and ltac: now require parentheses around
  their argument.
- Every generic argument type declares a tactic scope of the form "name:(...)"
  where name is the name of the argument. This generalizes the constr: and ltac:
  instances.
- When in strict mode (i.e. in a Ltac definition), if the "intro" tactic is
  given a free identifier, it is not bound in subsequent tactics anymore.
  In order to introduce a binding, use e.g. the "fresh" primitive instead
  (potential source of incompatibilities).
- New tactics is_ind, is_const, is_proj, is_constructor for use in Ltac.
- New goal selectors.  Sets of goals can be selected by listing integers
  ranges. Example: "1,4-7,24: tac" focuses "tac" on goals 1,4,5,6,7,24.
- For uniformity with "destruct"/"induction" and for a more natural
  behavior, "injection" can now work in place by activating option
  "Structural Injection". In this case, hypotheses are also put in the
  context in the natural left-to-right order and the hypothesis on
  which injection applies is cleared.
- Tactic "contradiction" (hence "easy") now also solve goals with
  hypotheses of the form "~True" or "t<>t" (possible source of
  incompatibilities because of more successes in automation, but
  generally a more intuitive strategy).
- Option "Injection On Proofs" was renamed "Keep Proof Equalities". When
  enabled, injection and inversion do not drop equalities between objects
  in Prop. Still disabled by default.
- New tactics "notypeclasses refine" and "simple notypeclasses refine" that
  disallow typeclass resolution when typechecking their argument, for use
  in typeclass hints.
- Integration of LtacProf, a profiler for Ltac.
- Reduction tactics now accept more fine-grained flags: iota is now a shorthand
  for the new flags match, fix and cofix.
- The ssreflect subterm selection algorithm is now accessible to tactic writers
  through the ssrmatching plugin.
- When used as an argument of an ltac function, "auto" without "with"
  nor "using" clause now correctly uses only the core hint database by
  default.

Hints

- Revised the syntax of [Hint Cut] to follow standard notation for regexps.
- Hint Mode now accepts "!" which means that the mode matches only if the
  argument's head is not an evar (it goes under applications, casts, and
  scrutinees of matches and projections).
- Hints can now take an optional user-given pattern, used only by
  [typeclasses eauto] with the [Filtered Unification] option on.

Typeclasses

- Many new options and new engine based on the proof monad. The
  [typeclasses eauto] tactic is now a multi-goal, multi-success tactic.
  See reference manual for more information. It is planned to
  replace auto and eauto in the following version. The 8.5 resolution
  engine is still available to help solve compatibility issues.

Program

- The "Shrink Obligations" flag now applies to all obligations, not only
  those solved by the automatic tactic.
- "Shrink Obligations" is on by default and deprecated. Minor source of
  incompatibility for code relying on the precise arguments of
  obligations.

Notations

- "Bind Scope" can once again bind "Funclass" and "Sortclass".

General infrastructure

- New configurable warning system which can be controlled with the vernacular
  command "Set Warnings", or, under coqc/coqtop, with the flag "-w". In
  particular, the default is now that warnings are printed by coqc.
- In asynchronous mode, Coq is now capable of recovering from errors and
  continue processing the document.

Tools

- coqc accepts a -o option to specify the output file name
- coqtop accepts --print-version to print Coq and OCaml versions in
  easy to parse format
- Setting [Printing Dependent Evars Line] can be unset to disable the
  computation associated with printing the "dependent evars: " line in
  -emacs mode
- Removed the -verbose-compat-notations flag and the corresponding Set
  Verbose Compat vernacular, since these warnings can now be silenced or
  turned into errors using "-w".

XML protocol

- message format has changed, see dev/doc/changes.txt for more details.

Many bug fixes, minor changes and documentation improvements are not mentioned
here.

Details of changes in 8.6
~~~~~~~~~~~~~~~~~~~~~~~~~

Kernel

- Fixed critical bug #5248 in VM long multiplication on 32-bit
  architectures. Was there only since 8.6beta1, so no stable release impacted.

Other bug fixes in universes, type class shelving,...

Details of changes in 8.6.1
~~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fix #5380: Default colors for CoqIDE are actually applied.
- Fix plugin warnings
- Document named evars (including Show ident)
- Fix Bug #5574, document function scope
- Adding a test case as requested in bug 5205.
- Fix Bug #5568, no dup notation warnings on repeated module imports
- Fix documentation of Typeclasses eauto :=
- Refactor documentation of records.
- Protecting from warnings while compiling 8.6
- Fixing an inconsistency between configure and configure.ml
- Add test-suite checks for coqchk with constraints
- Fix bug #5019 (looping zify on dependent types)
- Fix bug 5550: "typeclasses eauto with" does not work with section variables.
- Bug 5546, qualify datatype constructors when needed in Show Match
- Bug #5535, test for Show with -emacs
- Fix bug #5486, don't reverse ids in tuples
- Fixing #5522 (anomaly with free vars of pat)
- Fix bug #5526, don't check for nonlinearity in notation if printing only
- Fix bug #5255
- Fix bug #3659: -time should understand multibyte encodings.
- FIx bug #5300: Anomaly: Uncaught exception Not_found" in "Print Assumptions".
- Fix outdated description in RefMan.
- Repairing `Set Rewriting Schemes`
- Fixing #5487 (v8.5 regression on ltac-matching expressions with evars).
- Fix description of command-line arguments for Add (Rec) LoadPath
- Fix bug #5377: @? patterns broken.
- add XML protocol doc
- Fix anomaly when doing [all:Check _.] during a proof.
- Correction of bug #4306
- Fix #5435: [Eval native_compute in] raises anomaly.
- Instances should obey universe binders even when defined by tactics.
- Intern names bound in match patterns
- funind: Ignore missing info for current function
- Do not typecheck twice the type of opaque constants.
- show unused intro pattern warning
- [future] Be eager when "chaining" already resolved future values.
- Opaque side effects
- Fix #5132: coq_makefile generates incorrect install goal
- Run non-tactic comands without resilient_command
- Univs: fix bug #5365, generation of u+k <= v constraints
- make ``emit`` tail recursive
- Don't require printing-only notation to be productive
- Fix the way setoid_rewrite handles bindings.
- Fix for bug 5244 - set printing width ignored when given enough space
- Fix bug 4969, autoapply was not tagging shelved subgoals correctly

Version 8.5
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

Coq version 8.5 contains the result of five specific long-term projects:

-  A new asynchronous evaluation and compilation mode by Enrico Tassi
   with help from Bruno Barras and Carst Tankink.

-  Full integration of the new proof engine by Arnaud Spiwack helped by
   Pierre-Marie Pédrot,

-  Addition of conversion and reduction based on native compilation by
   Maxime Dénès and Benjamin Grégoire.

-  Full universe polymorphism for definitions and inductive types by
   Matthieu Sozeau.

-  An implementation of primitive projections with
   :math:`\eta`\-conversion bringing significant performance improvements
   when using records by Matthieu Sozeau.

The full integration of the proof engine, by Arnaud Spiwack and
Pierre-Marie Pédrot, brings to primitive tactics and the user level Ltac
language dependent subgoals, deep backtracking and multiple goal
handling, along with miscellaneous features and an improved potential
for future modifications. Dependent subgoals allow statements in a goal
to mention the proof of another. Proofs of unsolved subgoals appear as
existential variables. Primitive backtracking makes it possible to write
a tactic with several possible outcomes which are tried successively
when subsequent tactics fail. Primitives are also available to control
the backtracking behavior of tactics. Multiple goal handling paves the
way for smarter automation tactics. It is currently used for simple goal
manipulation such as goal reordering.

The way |Coq| processes a document in batch and interactive mode has been
redesigned by Enrico Tassi with help from Bruno Barras. Opaque proofs,
the text between Proof and Qed, can be processed asynchronously,
decoupling the checking of definitions and statements from the checking
of proofs. It improves the responsiveness of interactive development,
since proofs can be processed in the background. Similarly, compilation
of a file can be split into two phases: the first one checking only
definitions and statements and the second one checking proofs. A file
resulting from the first phase – with the .vio extension – can be
already Required. All .vio files can be turned into complete .vo files
in parallel. The same infrastructure also allows terminating tactics to
be run in parallel on a set of goals via the ``par:`` goal selector.

|CoqIDE| was modified to cope with asynchronous checking of the document.
Its source code was also made separate from that of |Coq|, so that |CoqIDE|
no longer has a special status among user interfaces, paving the way for
decoupling its release cycle from that of |Coq| in the future.

Carst Tankink developed a |Coq| back-end for user interfaces built on
Makarius Wenzel’s Prover IDE framework (PIDE), like PIDE/jEdit (with
help from Makarius Wenzel) or PIDE/Coqoon (with help from Alexander
Faithfull and Jesper Bengtson). The development of such features was
funded by the Paral-ITP French ANR project.

The full universe polymorphism extension was designed by Matthieu
Sozeau. It conservatively extends the universes system and core calculus
with definitions and inductive declarations parameterized by universes
and constraints. It is based on a modification of the kernel
architecture to handle constraint checking only, leaving the generation
of constraints to the refinement/type inference engine. Accordingly,
tactics are now fully universe aware, resulting in more localized error
messages in case of inconsistencies and allowing higher-level algorithms
like unification to be entirely type safe. The internal representation
of universes has been modified but this is invisible to the user.

The underlying logic has been extended with :math:`\eta`\-conversion for
records defined with primitive projections by Matthieu Sozeau. This
additional form of :math:`\eta`\-conversion is justified using the same
principle than the previously added :math:`\eta`\-conversion for function
types, based on formulations of the Calculus of Inductive Constructions
with typed equality. Primitive projections, which do not carry the
parameters of the record and are rigid names (not defined as a
pattern matching construct), make working with nested records more
manageable in terms of time and space consumption. This extension and
universe polymorphism were carried out partly while Matthieu Sozeau was
working at the IAS in Princeton.

The guard condition has been made compliant with extensional equality
principles such as propositional extensionality and univalence, thanks
to Maxime Dénès and Bruno Barras. To ensure compatibility with the
univalence axiom, a new flag ``-indices-matter`` has been implemented,
taking into account the universe levels of indices when computing the
levels of inductive types. This supports using |Coq| as a tool to explore
the relations between homotopy theory and type theory.

Maxime Dénès and Benjamin Grégoire developed an implementation of
conversion test and normal form computation using the OCaml native
compiler. It complements the virtual machine conversion offering much
faster computation for expensive functions.

Coq 8.5 also comes with a bunch of many various smaller-scale changes
and improvements regarding the different components of the system. We
shall only list a few of them.

Pierre Boutillier developed an improved tactic for simplification of
expressions called :tacn:`cbn`.

Maxime Dénès maintained the bytecode-based reduction machine. Pierre
Letouzey maintained the extraction mechanism.

Pierre-Marie Pédrot has extended the syntax of terms to, experimentally,
allow holes in terms to be solved by a locally specified tactic.

Existential variables are referred to by identifiers rather than mere
numbers, thanks to Hugo Herbelin who also improved the tactic language
here and there.

Error messages for universe inconsistencies have been improved by
Matthieu Sozeau. Error messages for unification and type inference
failures have been improved by Hugo Herbelin, Pierre-Marie Pédrot and
Arnaud Spiwack.

Pierre Courtieu contributed new features for using |Coq| through Proof
General and for better interactive experience (bullets, Search, etc).

The efficiency of the whole system has been significantly improved
thanks to contributions from Pierre-Marie Pédrot.

A distribution channel for |Coq| packages using the OPAM tool has been
initiated by Thomas Braibant and developed by Guillaume Claret, with
contributions by Enrico Tassi and feedback from Hugo Herbelin.

Packaging tools were provided by Pierre Letouzey and Enrico Tassi
(Windows), Pierre Boutillier, Matthieu Sozeau and Maxime Dénès (MacOS
X). Maxime Dénès improved significantly the testing and benchmarking
support.

Many power users helped to improve the design of the new features via
the bug tracker, the coq development mailing list or the Coq-Club
mailing list. Special thanks are going to the users who contributed
patches and intensive brain-storming, starting with Jason Gross,
Jonathan Leivent, Greg Malecha, Clément Pit-Claudel, Marc Lasson, Lionel
Rieg. It would however be impossible to mention with precision all names
of people who to some extent influenced the development.

Version 8.5 is one of the most important releases of |Coq|. Its development
spanned over about 3 years and a half with about one year of
beta-testing. General maintenance during part or whole of this period
has been done by Pierre Boutillier, Pierre Courtieu, Maxime Dénès, Hugo
Herbelin, Pierre Letouzey, Guillaume Melquiond, Pierre-Marie Pédrot,
Matthieu Sozeau, Arnaud Spiwack, Enrico Tassi as well as Bruno Barras,
Yves Bertot, Frédéric Besson, Xavier Clerc, Pierre Corbineau,
Jean-Christophe Filliâtre, Julien Forest, Sébastien Hinderer, Assia
Mahboubi, Jean-Marc Notin, Yann Régis-Gianas, François Ripault, Carst
Tankink. Maxime Dénès coordinated the release process.

| Paris, January 2015, revised December 2015,
| Hugo Herbelin, Matthieu Sozeau and the |Coq| development team
|

Potential sources of incompatibilities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

List of typical changes to be done to adapt files from Coq 8.4
to Coq 8.5 when not using compatibility option ``-compat 8.4``.

- Symptom: "The reference omega was not found in the current environment".

  Cause: "Require Omega" does not import the tactic "omega" any more

  Possible solutions:

  + use "Require Import OmegaTactic" (not compatible with 8.4)
  + use "Require Import Omega" (compatible with 8.4)
  + add definition "Ltac omega := Coq.omega.Omega.omega."

- Symptom: "intuition" cannot solve a goal (not working anymore on non standard connective)

  Cause: "intuition" had an accidental non uniform behavior fixed on non standard connectives

  Possible solutions:

  + use "dintuition" instead; it is stronger than "intuition" and works
    uniformly on non standard connectives, such as n-ary conjunctions or disjunctions
    (not compatible with 8.4)
  + do the script differently

- Symptom: The constructor foo (in type bar) expects n arguments.

  Cause: parameters must now be given in patterns

  Possible solutions:

  + use option "Set Asymmetric Patterns" (compatible with 8.4)
  + add "_" for the parameters (not compatible with 8.4)
  + turn the parameters into implicit arguments (compatible with 8.4)

- Symptom: "NPeano.Nat.foo" not existing anymore\

  Possible solutions:

  + use "Nat.foo" instead

  Symptom: typing problems with proj1_sig or similar

  Cause: coercion from sig to sigT and similar coercions have been
  removed so as to make the initial state easier to understand for
  beginners

  Solution: change proj1_sig into projT1 and similarly (compatible with 8.4)

Other detailed changes

- options for *coq* compilation (see below for ocaml).

  + [-I foo] is now deprecated and will not add directory foo to the
    coq load path (only for ocaml, see below). Just replace [-I foo] by
    [-Q foo ""] in your project file and re-generate makefile. Or
    perform the same operation directly in your makefile if you edit it
    by hand.

  + Option -R Foo bar is the same in v8.5 than in v8.4 concerning coq
    load path.

  + Option [-I foo -as bar] is unchanged but discouraged unless you
    compile ocaml code. Use -Q foo bar instead.

  for more details: see section "Customization at launch
  time" of the reference manual.

- Command line options for ocaml  Compilation of ocaml code (plugins)

  + [-I foo] is *not* deprecated to add foo to the ocaml load path.

  + [-I foo -as bar] adds foo to the ocaml load path *and* adds foo to
    the coq load path with logical name bar (shortcut for -I foo -Q foo
    bar).

  for more details: section "Customization at launch
  time" of the reference manual.

- Universe Polymorphism.

- Refinement, unification and tactics are now aware of universes,
  resulting in more localized errors. Universe inconsistencies
  should no more get raised at Qed time but during the proof.
  Unification *always* produces well-typed substitutions, hence
  some rare cases of unifications that succeeded while producing
  ill-typed terms before will now fail.

- The [change p with c] tactic semantics changed, now typechecking
  [c] at each matching occurrence [t] of the pattern [p], and
  converting [t] with [c].

- Template polymorphic inductive types: the partial application
  of a template polymorphic type (e.g. list) is not polymorphic.
  An explicit parameter application (e.g [fun A => list A]) or
  [apply (list _)] will result in a polymorphic instance.

- The type inference algorithm now takes opacity of constants into
  account. This may have effects on tactics using type inference
  (e.g. induction). Extra "Transparent" might have to be added to
  revert opacity of constants.

Type classes.

- When writing an ``Instance foo : Class A := {| proj := t |}`` (note the
  vertical bars), support for typechecking the projections using the
  type information and switching to proof mode is no longer available.
  Use ``{ }`` (without the vertical bars) instead.

Tactic abstract.

- Auxiliary lemmas generated by the abstract tactic are removed from
  the global environment and inlined in the proof term when a proof
  is ended with Qed.  The behavior of 8.4 can be obtained by ending
  proofs with "Qed exporting" or "Qed exporting ident, .., ident".

Details of changes in 8.5beta1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Logic

- Primitive projections for records allow for a compact representation
  of projections, without parameters and avoid the behavior of defined
  projections that can unfold to a case expression. To turn the use of
  native projections on, use [Set Primitive Projections]. Record,
  Class and Structure types defined while this option is set will be
  defined with primitive projections instead of the usual encoding as
  a case expression. For compatibility, when p is a primitive
  projection, @p can be used to refer to the projection with explicit
  parameters, i.e. [@p] is definitionally equal to [λ params r. r.(p)].
  Records with primitive projections have eta-conversion, the
  canonical form being [mkR pars (p1 t) ... (pn t)].
- New universe polymorphism (see reference manual)
- New option -type-in-type to collapse the universe hierarchy (this makes the
  logic inconsistent).
- The guard condition for fixpoints is now a bit stricter. Propagation
  of subterm value through pattern matching is restricted according to
  the return predicate. Restores compatibility of Coq's logic with the
  propositional extensionality axiom. May create incompatibilities in
  recursive programs heavily using dependent types.
- Trivial inductive types are no longer defined in Type but in Prop, which
  leads to a non-dependent induction principle being generated in place of
  the dependent one. To recover the old behavior, explicitly define your
  inductive types in Set.

Vernacular commands

- A command "Variant" allows to define non-recursive variant types.
- The command "Record foo ..." does not generate induction principles
  (foo_rect, foo_rec, foo_ind) anymore by default (feature wish
  #2693). The command "Variant foo ..." does not either. A flag
  "Set/Unset Nonrecursive Elimination Schemes" allows changing this.
  The tactic "induction" on a "Record" or a "Variant" is now actually
  doing "destruct".
- The "Open Scope" command can now be given also a delimiter (e.g. Z).
- The "Definition" command now allows the "Local" modifier, allowing
  for non-importable definitions. The same goes for "Axiom" and "Parameter".
- Section-specific commands such as "Let" (resp. "Variable", "Hypothesis") used
  out of a section now behave like the corresponding "Local" command, i.e.
  "Local Definition" (resp. "Local Parameter", "Local Axiom"). (potential source
  of rare incompatibilities).
- The "Let" command can now define local (co)fixpoints.
- Command "Search" has been renamed into "SearchHead". The command
  name "Search" now behaves like former "SearchAbout". The latter name
  is deprecated.
- "Search", "About", "SearchHead", "SearchRewrite" and "SearchPattern"
  now search for hypothesis (of the current goal by default) first.
  They now also support the goal selector prefix to specify another
  goal to search: e.g. "n:Search id". This is also true for
  SearchAbout although it is deprecated.
- The coq/user-contrib directory and the XDG directories are no longer
  recursively added to the load path, so files from installed libraries
  now need to be fully qualified for the "Require" command to find them.
  The tools/update-require script can be used to convert a development.
- A new Print Strategies command allows visualizing the opacity status
  of the whole engine.
- The "Locate" command now searches through all sorts of qualified namespaces of
  Coq: terms, modules, tactics, etc. The old behavior of the command can be
  retrieved using the "Locate Term" command.
- New "Derive" command to help writing program by derivation.
- New "Refine Instance Mode" option that allows to deactivate the generation of
  obligations in incomplete typeclass instances, raising an error instead.
- "Collection" command to name sets of section hypotheses.  Named collections
  can be used in the syntax of "Proof using" to assert which section variables
  are used in a proof.
- The "Optimize Proof" command can be placed in the middle of a proof to
  force the compaction of the data structure used to represent the ongoing
  proof (evar map). This may result in a lower memory footprint and speed up
  the execution of the following tactics.
- "Optimize Heap" command to tell the OCaml runtime to perform a major
  garbage collection step and heap compaction.
- ``Instance`` no longer treats the ``{|...|}`` syntax specially; it handles it
  in the same way as other commands, e.g. "Definition". Use the ``{...}``
  syntax (no pipe symbols) to recover the old behavior.

Specification Language

- Slight changes in unification error messages.
- Added a syntax $(...)$ that allows putting tactics in terms (may
  break user notations using "$(", fixable by inserting a space or
  rewriting the notation).
- Constructors in pattern-matching patterns now respect the same rules
  regarding implicit arguments as in applicative position. The old
  behavior can be recovered by the command "Set Asymmetric
  Patterns". As a side effect, notations for constructors explicitly
  mentioning non-implicit parameters can now be used in patterns.
  Considering that the pattern language is already rich enough, binding
  local definitions is however now forbidden in patterns (source of
  incompatibilities for local definitions that delta-reduce to a constructor).
- Type inference algorithm now granting opacity of constants. This might also
  affect behavior of tactics (source of incompatibilities, solvable by
  re-declaring transparent constants which were set opaque).
- Existential variables are now referred to by an identifier and the
  relevant part of their instance is displayed by default. They can be
  reparsed. The naming policy is yet unstable and subject to changes
  in future releases.

Tactics

- New tactic engine allowing dependent subgoals, fully backtracking
  (also known as multiple success) tactics, as well as tactics which
  can consider multiple goals together. In the new tactic engine,
  instantiation information of existential variables is always
  propagated to tactics, removing the need to manually use the
  "instantiate" tactics to mark propagation points.

  * New tactical (a+b) inserts a backtracking point. When (a+b);c fails
    during the execution of c, it can backtrack and try b instead of a.
  * New tactical (once a) removes all the backtracking points from a
    (i.e. it selects the first success of a).
  * Tactic "constructor" is now fully backtracking. In case of
    incompatibilities (e.g. combinatoric explosion), the former
    behavior of "constructor" can be retrieved by using instead
    "[> once constructor ..]". Thanks to backtracking, undocumented
    "constructor <tac>" syntax is now equivalent to
    "[> once (constructor; tac) ..]".
  * New "multimatch" variant of "match" tactic which backtracks to
    new branches in case of a later failure. The "match" tactic is
    equivalent to "once multimatch".
  * New selector "all:" such that "all:tac" applies tactic "tac" to
    all the focused goals, instead of just the first one as is the
    default.
  * A corresponding new option Set Default Goal Selector "all" makes
    the tactics in scripts be applied to all the focused goal by default
  * New selector "par:" such that "par:tac" applies the (terminating)
    tactic "tac" to all the focused goal in parallel. The number of worker
    can be selected with -async-proofs-tac-j and also limited using the
    coqworkmgr utility.
  * New tactics "revgoals", "cycle" and "swap" to reorder goals.
  * The semantics of recursive tactics (introduced with "Ltac t := ..."
    or "let rec t := ... in ...") changed slightly as t is now
    applied to every goal, not each goal independently. In particular
    it may be applied when no goals are left. This may cause tactics
    such as "let rec t := constructor;t" to loop indefinitely. The
    simple fix is to rewrite the recursive calls as follows:
    "let rec t := constructor;[t..]" which recovers the earlier behavior
    (source of rare incompatibilities).
  * New tactic language feature "numgoals" to count number of goals. It is
    accompanied by a "guard" tactic which fails if a Boolean test over
    integers does not pass.
  * New tactical "[> ... ]" to apply tactics to individual goals.
  * New tactic "gfail" which works like "fail" except it will also
    fail if every goal has been solved.
  * The refine tactic is changed not to use an ad hoc typing algorithm
    to generate subgoals. It also uses the dependent subgoal feature
    to generate goals to materialize every existential variable which
    is introduced by the refinement (source of incompatibilities).
  * A tactic shelve is introduced to manage the subgoals which may be
    solved by unification: shelve removes every goal it is applied to
    from focus. These goals can later be called back into focus by the
    Unshelve command.
  * A variant shelve_unifiable only removes those goals which appear
    as existential variables in other goals. To emulate the old
    refine, use "refine c;shelve_unifiable". This can still cause
    incompatibilities in rare occasions.
  * New "give_up" tactic to skip over a goal.  A proof containing
    given up goals cannot be closed with "Qed", but only with "Admitted".

- The implementation of the admit tactic has changed: no axiom is
  generated for the admitted sub proof. "admit" is now an alias for
  "give_up".  Code relying on this specific behavior of "admit"
  can be made to work by:

  * Adding an "Axiom" for each admitted subproof.
  * Adding a single "Axiom proof_admitted : False." and the Ltac definition
    "Ltac admit := case proof_admitted.".

- Matching using "lazymatch" was fundamentally modified. It now behaves
  like "match" (immediate execution of the matching branch) but without
  the backtracking mechanism in case of failure.

- New "tryif t then u else v" tactical which executes "u" in case of success
  of "t" and "v" in case of failure.

- New conversion tactic "native_compute": evaluates the goal (or an hypothesis)
  with a call-by-value strategy, using the OCaml native compiler. Useful on
  very intensive computations.

- New "cbn" tactic, a well-behaved simpl.

- Repeated identical calls to omega should now produce identical proof terms.

- Tactics btauto, a reflexive Boolean tautology solver.

- Tactic "tauto" was exceptionally able to destruct other connectives
  than the binary connectives "and", "or", "prod", "sum", "iff". This
  non-uniform behavior has been fixed (bug #2680) and tauto is
  slightly weaker (possible source of incompatibilities). On the
  opposite side, new tactic "dtauto" is able to destruct any
  record-like inductive types, superseding the old version of "tauto".

- Similarly, "intuition" has been made more uniform and, where it now
  fails, "dintuition" can be used (possible source of incompatibilities).

- New option "Unset Intuition Negation Unfolding" for deactivating automatic
  unfolding of "not" in intuition.

- Tactic notations can now be defined locally to a module (use "Local" prefix).

- Tactic "red" now reduces head beta-iota redexes (potential source of
  rare incompatibilities).

- Tactic "hnf" now reduces inner beta-iota redexes
  (potential source of rare incompatibilities).

- Tactic "intro H" now reduces beta-iota redexes if these hide a product
  (potential source of rare incompatibilities).

- In Ltac matching on patterns of the form "_ pat1 ... patn" now
  behaves like if matching on "?X pat1 ... patn", i.e. accepting "_"
  to be instantiated by an applicative term (experimental at this
  stage, potential source of incompatibilities).

- In Ltac matching on goal, types of hypotheses are now interpreted in
  the %type scope (possible source of incompatibilities).

- "change ... in ..." and "simpl ... in ..." now properly consider nested
  occurrences (possible source of incompatibilities since this alters
  the numbering of occurrences), but do not support nested occurrences.

- Tactics simpl, vm_compute and native_compute can be given a notation string
  to a constant as argument.

- When given a reference as argument, simpl, vm_compute and
  native_compute now strictly interpret it as the head of a pattern
  starting with this reference.

- The "change p with c" tactic semantics changed, now type-checking
  "c" at each matching occurrence "t" of the pattern "p", and
  converting "t" with "c".

- Now "appcontext" and "context" behave the same. The old buggy behavior of
  "context" can be retrieved at parse time by setting the
  "Tactic Compat Context" flag (possible source of incompatibilities).

- New introduction pattern p/c which applies lemma c on the fly on the
  hypothesis under consideration before continuing with introduction pattern p.

- New introduction pattern [= x1 .. xn] applies "injection as [x1 .. xn]"
  on the fly if injection is applicable to the hypothesis under consideration
  (idea borrowed from Georges Gonthier). Introduction pattern [=] applies
  "discriminate" if a discriminable equality.

- New introduction patterns * and ** to respectively introduce all forthcoming
  dependent variables and all variables/hypotheses dependent or not.

- Tactic "injection c as ipats" now clears c if c refers to an
  hypothesis and moves the resulting equations in the hypotheses
  independently of the number of ipats, which has itself to be less
  than the number of new hypotheses (possible source of incompatibilities;
  former behavior obtainable by "Unset Injection L2R Pattern Order").

- Tactic "injection" now automatically simplifies subgoals
  "existT n p = existT n p'" into "p = p'" when "n" is in an inductive type for
  which a decidable equality scheme has been generated with "Scheme Equality"
  (possible source of incompatibilities).

- New tactic "rewrite_strat" for generalized rewriting with user-defined
  strategies, subsuming autorewrite.

- Injection can now also deduce equality of arguments of sort Prop, by using
  the option "Set Injection On Proofs" (disabled by default). Also improved the
  error messages.

- Tactic "subst id" now supports id occurring in dependent local definitions.

- Bugs fixed about intro-pattern "*" might lead to some rare incompatibilities.

- New tactical "time" to display time spent executing its argument.

- Tactics referring or using a constant dependent in a section variable which
  has been cleared or renamed in the current goal context now fail
  (possible source of incompatibilities solvable by avoiding clearing
  the relevant hypotheses).

- New construct "uconstr:c" and "type_term c" to build untyped terms.

- Binders in terms defined in Ltac (either "constr" or "uconstr") can
  now take their names from identifiers defined in Ltac. As a
  consequence, a name cannot be used in a binder "constr:(fun x =>
  ...)" if an Ltac variable of that name already exists and does not
  contain an identifier. Source of occasional incompatibilities.

- The "refine" tactic now accepts untyped terms built with "uconstr"
  so that terms with holes can be constructed piecewise in Ltac.

- New bullets --, ++, **, ---, +++, ***, ... made available.

- More informative messages when wrong bullet is used.

- Bullet suggestion when a subgoal is solved.

- New tactic "enough", symmetric to "assert", but with subgoals
  swapped, as a more friendly replacement of "cut".

- In destruct/induction, experimental modifier "!" prefixing the
  hypothesis name to tell not erasing the hypothesis.

- Bug fixes in "inversion as" may occasionally lead to incompatibilities.

- Behavior of introduction patterns -> and <- made more uniform
  (hypothesis is cleared, rewrite in hypotheses and conclusion and
  erasing the variable when rewriting a variable).

- New experimental option "Set Standard Proposition Elimination Names"
  so that case analysis or induction on schemes in Type containing
  propositions now produces "H"-based names.

- Tactics from plugins are now active only when the corresponding module
  is imported (source of incompatibilities, solvable by adding an "Import";
  in the particular case of Omega, use "Require Import OmegaTactic").

- Semantics of destruct/induction has been made more regular in some
  edge cases, possibly leading to incompatibilities:

  + new goals are now opened when the term does not match a subterm of
    the goal and has unresolved holes, while in 8.4 these holes were
    turned into existential variables
  + when no "at" option is given, the historical semantics which
    selects all subterms syntactically identical to the first subterm
    matching the given pattern is used
  + non-dependent destruct/induction on an hypothesis with premises in
    an inductive type with indices is fixed
  + residual local definitions are now correctly removed.

- The rename tactic may now replace variables in parallel.

- A new "Info" command replaces the "info" tactical discontinued in
  v8.4. It still gives informative results in many cases.

- The "info_auto" tactic is known to be broken and does not print a
  trace anymore. Use "Info 1 auto" instead. The same goes for
  "info_trivial". On the other hand "info_eauto" still works fine,
  while "Info 1 eauto" prints a trivial trace.

- When using a lemma of the prototypical form "forall A, {a:A & P a}",
  "apply" and "apply in" do not instantiate anymore "A" with the
  current goal and use "a" as the proof, as they were sometimes doing,
  now considering that it is a too powerful decision.

Program

- "Solve Obligations using" changed to "Solve Obligations with",
  consistent with "Proof with".
- Program Lemma, Definition now respect automatic introduction.
- Program Lemma, Definition, etc.. now interpret "->" like Lemma and
  Definition as a non-dependent arrow (potential source of
  incompatibility).
- Add/document "Set Hide Obligations" (to hide obligations in the final
  term inside an implicit argument) and "Set Shrink Obligations" (to
  minimize dependencies of obligations defined by tactics).

Notations

- The syntax "x -> y" is now declared at level 99. In particular, it has
  now a lower priority than "<->": "A -> B <-> C" is now "A -> (B <-> C)"
  (possible source of incompatibilities)
- Notations accept term-providing tactics using the $(...)$ syntax.
- "Bind Scope" can no longer bind "Funclass" and "Sortclass".
- A notation can be given a (compat "8.x") annotation, making it behave
  like a "only parsing" notation, but the annotation may lead to eventually
  issue warnings or errors in further versions when this notation is used.
- More systematic insertion of spaces as a default for printing
  notations ("format" still available to override the default).
- In notations, a level modifier referring to a non-existent variable is
  now considered an error rather than silently ignored.

Tools

- Option -I now only adds directories to the ml path.
- Option -Q behaves as -R, except that the logical path of any loaded file has
  to be fully qualified.
- Option -R no longer adds recursively to the ml path; only the root
  directory is added. (Behavior with respect to the load path is
  unchanged.)
- Option -nois prevents coq/theories and coq/plugins to be recursively
  added to the load path. (Same behavior as with coq/user-contrib.)
- coqdep accepts a -dumpgraph option generating a dot file.
- Makefiles generated through coq_makefile have three new targets "quick"
  "checkproofs" and "vio2vo", allowing respectively to asynchronously compile
  the files without playing the proof scripts, asynchronously checking
  that the quickly generated proofs are correct and generating the object
  files from the quickly generated proofs.
- The XML plugin was discontinued and removed from the source.
- A new utility called coqworkmgr can be used to limit the number of
  concurrent workers started by independent processes, like make and CoqIDE.
  This is of interest for users of the par: goal selector.

Interfaces

- CoqIDE supports asynchronous edition of the document, ongoing tasks and
  errors are reported in the bottom right window.  The number of workers
  taking care of processing proofs can be selected with -async-proofs-j.
- CoqIDE highlights in yellow "unsafe" commands such as axiom
  declarations, and tactics like "give_up".
- CoqIDE supports Proof General like key bindings;
  to activate the PG mode go to Edit -> Preferences -> Editor.
  For the documentation see Help -> Help for PG mode.
- CoqIDE automatically retracts the locked area when one edits the
  locked text.
- CoqIDE search and replace got regular expressions power. See the
  documentation of OCaml's Str module for the supported syntax.
- Many CoqIDE windows, including the query one, are now detachable to
  improve usability on multi screen work stations.
- Coqtop/coqc outputs highlighted syntax. Colors can be configured thanks
  to the COQ_COLORS environment variable, and their current state can
  be displayed with the -list-tags command line option.
- Third party user interfaces can install their main loop in $COQLIB/toploop
  and call coqtop with the -toploop flag to select it.

Internal Infrastructure

- Many reorganizations in the ocaml source files. For instance,
  many internal a.s.t. of Coq are now placed in mli files in
  a new directory intf/, for instance constrexpr.mli or glob_term.mli.
  More details in dev/doc/changes.

- The file states/initial.coq does not exist anymore. Instead, coqtop
  initially does a "Require" of Prelude.vo (or nothing when given
  the options -noinit or -nois).

- The format of vo files has slightly changed: cf final comments in
  checker/cic.mli.

- The build system does not produce anymore programs named coqtop.opt
  and a symbolic link to coqtop. Instead, coqtop is now directly
  an executable compiled with the best OCaml compiler available.
  The bytecode program coqtop.byte is still produced. Same for other
  utilities.

- Some options of the ./configure script slightly changed:

  * The -coqrunbyteflags and its blank-separated argument is replaced
    by option -vmbyteflags which expects a comma-separated argument.
  * The -coqtoolsbyteflags option is discontinued, see -no-custom instead.

Miscellaneous

- ML plugins now require a "DECLARE PLUGIN \"foo\"" statement. The "foo" name
  must be exactly the name of the ML module that will be loaded through a
  "Declare ML \"foo\"" command.

Details of changes in 8.5beta2
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Logic

- The VM now supports inductive types with up to 8388851 non-constant
  constructors and up to 8388607 constant ones.

Specification language

- Syntax "$(tactic)$" changed to "ltac: tactic".

Tactics

- A script using the admit tactic can no longer be concluded by either
  Qed or Defined. In the first case, Admitted can be used instead. In
  the second case, a subproof should be used.
- The easy tactic and the now tactical now have a more predictable
  behavior, but they might now discharge some previously unsolved goals.

Extraction

- Definitions extracted to Haskell GHC should no longer randomly
  segfault when some Coq types cannot be represented by Haskell types.
- Definitions can now be extracted to Json for post-processing.

Tools

- Option -I -as has been removed, and option -R -as has been
  deprecated. In both cases, option -R can be used instead.
- coq_makefile now generates double-colon rules for rules such as clean.

API

- The interface of [change] has changed to take a [change_arg], which
  can be built from a [constr] using [make_change_arg].

Details of changes in 8.5beta3
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Vernacular commands

- New command "Redirect" to redirect the output of a command to a file.
- New command "Undelimit Scope" to remove the delimiter of a scope.
- New option "Strict Universe Declaration", set by default. It enforces the
  declaration of all polymorphic universes appearing in a definition when
  introducing it.
- New command "Show id" to show goal named id.
- Option "Virtual Machine" removed.

Tactics

- New flag "Regular Subst Tactic" which fixes "subst" in situations where
  it failed to substitute all substitutable equations or failed to simplify
  cycles, or accidentally unfolded local definitions (flag is off by default).
- New flag "Loose Hint Behavior" to handle hints loaded but not imported in a
  special way. It accepts three distinct flags:
  * "Lax", which is the default one, sets the old behavior, i.e. a non-imported
  hint behaves the same as an imported one.
  * "Warn" outputs a warning when a non-imported hint is used. Note that this is
  an over-approximation, because a hint may be triggered by an eauto run that
  will eventually fail and backtrack.
  * "Strict" changes the behavior of an unloaded hint to the one of the fail
  tactic, allowing to emulate the hopefully future import-scoped hint mechanism.
- New compatibility flag "Universal Lemma Under Conjunction" which
  let tactics working under conjunctions apply sublemmas of the form
  "forall A, ... -> A".
- New compatibility flag "Bracketing Last Introduction Pattern" which can be
  set so that the last disjunctive-conjunctive introduction pattern given to
  "intros" automatically complete the introduction of its subcomponents, as the
  the disjunctive-conjunctive introduction patterns in non-terminal position
  already do.
- New flag "Shrink Abstract" that minimalizes proofs generated by the abstract
  tactical w.r.t. variables appearing in the body of the proof.

Program

- The "Shrink Obligations" flag now applies to all obligations, not only those
  solved by the automatic tactic.
- Importing Program no longer overrides the "exists" tactic (potential source
  of incompatibilities).
- Hints costs are now correctly taken into account (potential source of
  incompatibilities).
- Documented the Hint Cut command that allows control of the
  proof-search during typeclass resolution (see reference manual).

API

- Some functions from pretyping/typing.ml and their derivatives were potential
  source of evarmap leaks, as they dropped their resulting evarmap. The
  situation was clarified by renaming them according to a ``unsafe_*`` scheme. Their
  sound variant is likewise renamed to their old name. The following renamings
  were made.

  * ``Typing.type_of`` -> ``unsafe_type_of``
  * ``Typing.e_type_of`` -> ``type_of``
  * A new ``e_type_of`` function that matches the ``e_`` prefix policy
  * ``Tacmach.pf_type_of`` -> ``pf_unsafe_type_of``
  * A new safe ``pf_type_of`` function.

  All uses of ``unsafe_*`` functions should be eventually eliminated.

Tools

- Added an option -w to control the output of coqtop warnings.
- Configure now takes an optional -native-compiler (yes|no) flag replacing
  -no-native-compiler. The new flag is set to no by default under Windows.
- Flag -no-native-compiler was removed and became the default for coqc. If
  precompilation of files for native conversion test is desired, use
  -native-compiler.
- The -compile command-line option now takes the full path of the considered
  file, including the ".v" extension, and outputs a warning if such an extension
  is lacking.
- The -require and -load-vernac-object command-line options now take a logical
  path of a given library rather than a physical path, thus they behave like
  Require [Import] path.
- The -vm command-line option has been removed.

Standard Library

 - There is now a Coq.Compat.Coq84 library, which sets the various compatibility
   options and does a few redefinitions to make Coq behave more like Coq v8.4.
   The standard way of putting Coq in v8.4 compatibility mode is to pass the command
   line flags "-require Coq.Compat.Coq84 -compat 8.4".

Details of changes in 8.5
~~~~~~~~~~~~~~~~~~~~~~~~~

Tools

- Flag "-compat 8.4" now loads Coq.Compat.Coq84. The standard way of
  putting Coq in v8.4 compatibility mode is to pass the command line flag
  "-compat 8.4". It can be followed by "-require Coq.Compat.AdmitAxiom"
  if the 8.4 behavior of admit is needed, in which case it uses an axiom.

Specification language

- Syntax "$(tactic)$" changed to "ltac:(tactic)".

Tactics

- Syntax "destruct !hyp" changed to "destruct (hyp)", and similarly
  for induction (rare source of incompatibilities easily solvable by
  removing parentheses around "hyp" when not for the purpose of keeping
  the hypothesis).
- Syntax "p/c" for on-the-fly application of a lemma c before
  introducing along pattern p changed to p%c1..%cn. The feature and
  syntax are in experimental stage.
- "Proof using" does not clear unused section variables.
- Tactic "refine" has been changed back to the 8.4 behavior of shelving subgoals
  that occur in other subgoals. The "refine" tactic of 8.5beta3 has been
  renamed "simple refine"; it does not shelve any subgoal.
- New tactical "unshelve tac" which grab existential variables put on
  the tactic shelve by the execution of "tac".

Details of changes in 8.5pl1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Critical bugfix

- The subterm relation for the guard condition was incorrectly defined on
  primitive projections (#4588)

Plugin development tools

- add a .merlin target to the makefile

Various performance improvements (time, space used by .vo files)

Other bugfixes

- Fix order of arguments to Big.compare_case in ExtrOcamlZBigInt.v
- Added compatibility coercions from Specif.v which were present in Coq 8.4.
- Fixing a source of inefficiency and an artificial dependency in the printer in the congruence tactic.
- Allow to unset the refinement mode of Instance in ML
- Fixing an incorrect use of prod_appvect on a term which was not a product in setoid_rewrite.
- Add -compat 8.4 econstructor tactics, and tests
- Add compatibility Nonrecursive Elimination Schemes
- Fixing the "No applicable tactic" non informative error message regression on apply.
- Univs: fix get_current_context (bug #4603, part I)
- Fix a bug in Program coercion code
- Fix handling of arity of definitional classes.
- #4630: Some tactics are 20x slower in 8.5 than 8.4.
- #4627: records with no declared arity can be template polymorphic.
- #4623: set tactic too weak with universes (regression)
- Fix incorrect behavior of CS resolution
- #4591: Uncaught exception in directory browsing.
- CoqIDE is more resilient to initialization errors.
- #4614: "Fully check the document" is uninterruptible.
- Try eta-expansion of records only on non-recursive ones
- Fix bug when a sort is ascribed to a Record
- Primitive projections: protect kernel from erroneous definitions.
- Fixed bug #4533 with previous Keyed Unification commit
- Win: kill unreliable hence do not waitpid after kill -9 (Close #4369)
- Fix strategy of Keyed Unification
- #4608: Anomaly "output_value: abstract value (outside heap)".
- #4607: do not read native code files if native compiler was disabled.
- #4105: poor escaping in the protocol between CoqIDE and coqtop.
- #4596: [rewrite] broke in the past few weeks.
- #4533 (partial): respect declared global transparency of projections in unification.ml
- #4544: Backtrack on using full betaiota reduction during keyed unification.
- #4540: CoqIDE bottom progress bar does not update.
- Fix regression from 8.4 in reflexivity
- #4580: [Set Refine Instance Mode] also used for Program Instance.
- #4582: cannot override notation [ x ]. MAY CREATE INCOMPATIBILITIES, see #4683.
- STM: Print/Extraction have to be skipped if -quick
- #4542: CoqIDE: STOP button also stops workers
- STM: classify some variants of Instance as regular `` `Fork `` nodes.
- #4574: Anomaly: Uncaught exception Invalid_argument("splay_arity").
- Do not give a name to anonymous evars anymore. See bug #4547.
- STM: always stock in vio files the first node (state) of a proof
- STM: not delegate proofs that contain Vernac(Module|Require|Import), #4530
- Don't fail fatally if PATH is not set.
- #4537: Coq 8.5 is slower in typeclass resolution.
- #4522: Incorrect "Warning..." on windows.
- #4373: coqdep does not know about .vio files.
- #3826: "Incompatible module types" is uninformative.
- #4495: Failed assertion in metasyntax.ml.
- #4511: evar tactic can create non-typed evars.
- #4503: mixing universe polymorphic and monomorphic variables and definitions in sections is unsupported.
- #4519: oops, global shadowed local universe level bindings.
- #4506: Anomaly: File "pretyping/indrec.ml", line 169, characters 14-20: Assertion failed.
- #4548: Coqide crashes when going back one command

Details of changes in 8.5pl2
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Critical bugfix

- Checksums of .vo files dependencies were not correctly checked.
- Unicode-to-ASCII translation was not injective, leading in a soundness bug in
  the native compiler.

Other bugfixes

- #4097: more efficient occur-check in presence of primitive projections
- #4398: type_scope used consistently in "match goal".
- #4450: eauto does not work with polymorphic lemmas
- #4677: fix alpha-conversion in notations needing eta-expansion.
- Fully preserve initial order of hypotheses in "Regular Subst Tactic" mode.
- #4644: a regression in unification.
- #4725: Function (Error: Conversion test raised an anomaly) and Program
  (Error: Cannot infer this placeholder of type)
- #4747: Problem building Coq 8.5pl1 with OCaml 4.03.0: Fatal warnings
- #4752: CoqIDE crash on files not ended by ".v".
- #4777: printing inefficiency with implicit arguments
- #4818: "Admitted" fails due to undefined universe anomaly after calling
  "destruct"
- #4823: remote counter: avoid thread race on sockets
- #4841: -verbose flag changed semantics in 8.5, is much harder to use
- #4851: [nsatz] cannot handle duplicated hypotheses
- #4858: Anomaly: Uncaught exception Failure("hd"). Please report. in variant
  of nsatz
- #4880: [nsatz_compute] generates invalid certificates if given redundant
  hypotheses
- #4881: synchronizing "Declare Implicit Tactic" with backtrack.
- #4882: anomaly with Declare Implicit Tactic on hole of type with evars
- Fix use of "Declare Implicit Tactic" in refine.
  triggered by CoqIDE
- #4069, #4718: congruence fails when universes are involved.

Universes

- Disallow silently dropping universe instances applied to variables
  (forward compatible)
- Allow explicit universe instances on notations, when they can apply
  to the head reference of their expansion.

Build infrastructure

- New update on how to find camlp5 binary and library at configure time.

Details of changes in 8.5pl3
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Critical bugfix

- #4876: Guard checker incompleteness when using primitive projections

Other bugfixes

- #4780: Induction with universe polymorphism on was creating ill-typed terms.
- #4673: regression in setoid_rewrite, unfolding let-ins for type unification.
- #4754: Regression in setoid_rewrite, allow postponed unification problems to remain.
- #4769: Anomaly with universe polymorphic schemes defined inside sections.
- #3886: Program: duplicate obligations of mutual fixpoints.
- #4994: Documentation typo.
- #5008: Use the "md5" command on OpenBSD.
- #5007: Do not assume the "TERM" environment variable is always set.
- #4606: Output a break before a list only if there was an empty line.
- #5001: metas not cleaned properly in clenv_refine_in.
- #2336: incorrect glob data for module symbols (bug #2336).
- #4832: Remove extraneous dot in error message.
- Anomaly in printing a unification error message.
- #4947: Options which take string arguments are not backwards compatible.
- #4156: micromega cache files are now hidden files.
- #4871: interrupting par:abstract kills coqtop.
- #5043: [Admitted] lemmas pick up section variables.
- Fix name of internal refine ("simple refine").
- #5062: probably a typo in Strict Proofs mode.
- #5065: Anomaly: Not a proof by induction.
- Restore native compiler optimizations, they were disabled since 8.5!
- #5077: failure on typing a fixpoint with evars in its type.
- Fix recursive notation bug.
- #5095: non relevant too strict test in let-in abstraction.
- Ensuring that the evar name is preserved by "rename".
- #4887: confusion between using and with in documentation of firstorder.
- Bug in subst with let-ins.
- #4762: eauto weaker than auto.
- Remove if_then_else (was buggy). Use tryif instead.
- #4970: confusion between special "{" and non special "{{" in notations.
- #4529: primitive projections unfolding.
- #4416: Incorrect "Error: Incorrect number of goals".
- #4863: abstract in typeclass hint fails.
- #5123: unshelve can impact typeclass resolution
- Fix a collision about the meta-variable ".." in recursive notations.
- Fix printing of info_auto.
- #3209: Not_found due to an occur-check cycle.
- #5097: status of evars refined by "clear" in ltac: closed wrt evars.
- #5150: Missing dependency of the test-suite subsystems in prerequisite.
- Fix a bug in error printing of unif constraints
- #3941: Do not stop propagation of signals when Coq is busy.
- #4822: Incorrect assertion in cbn.
- #3479 parsing of "{" and "}" when a keyword starts with "{" or "}".
- #5127: Memory corruption with the VM.
- #5102: bullets parsing broken by calls to parse_entry.

Various documentation improvements

Version 8.4
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

Coq version 8.4 contains the result of three long-term projects: a new
modular library of arithmetic by Pierre Letouzey, a new proof engine by
Arnaud Spiwack and a new communication protocol for |CoqIDE| by Vincent
Gross.

The new modular library of arithmetic extends, generalizes and unifies
the existing libraries on Peano arithmetic (types nat, N and BigN),
positive arithmetic (type positive), integer arithmetic (Z and BigZ) and
machine word arithmetic (type Int31). It provides with unified notations
(e.g. systematic use of add and mul for denoting the addition and
multiplication operators), systematic and generic development of
operators and properties of these operators for all the types mentioned
above, including gcd, pcm, power, square root, base 2 logarithm,
division, modulo, bitwise operations, logical shifts, comparisons,
iterators, ...

The most visible feature of the new proof engine is the support for
structured scripts (bullets and proof brackets) but, even if yet not
user-available, the new engine also provides the basis for refining
existential variables using tactics, for applying tactics to several
goals simultaneously, for reordering goals, all features which are
planned for the next release. The new proof engine forced Pierre Letouzey
to reimplement info and Show Script differently.

Before version 8.4, |CoqIDE| was linked to |Coq| with the graphical
interface living in a separate thread. From version 8.4, |CoqIDE| is a
separate process communicating with |Coq| through a textual channel. This
allows for a more robust interfacing, the ability to interrupt |Coq|
without interrupting the interface, and the ability to manage several
sessions in parallel. Relying on the infrastructure work made by Vincent
Gross, Pierre Letouzey, Pierre Boutillier and Pierre-Marie Pédrot
contributed many various refinements of |CoqIDE|.

Coq 8.4 also comes with a bunch of various smaller-scale changes
and improvements regarding the different components of the system.

The underlying logic has been extended with :math:`\eta`-conversion
thanks to Hugo Herbelin, Stéphane Glondu and Benjamin Grégoire. The
addition of :math:`\eta`-conversion is justified by the confidence that
the formulation of the Calculus of Inductive Constructions based on
typed equality (such as the one considered in Lee and Werner to build a
set-theoretic model of CIC :cite:`LeeWerner11`) is
applicable to the concrete implementation of |Coq|.

The underlying logic benefited also from a refinement of the guard
condition for fixpoints by Pierre Boutillier, the point being that it is
safe to propagate the information about structurally smaller arguments
through :math:`\beta`-redexes that are blocked by the “match”
construction (blocked commutative cuts).

Relying on the added permissiveness of the guard condition, Hugo
Herbelin could extend the pattern matching compilation algorithm so that
matching over a sequence of terms involving dependencies of a term or of
the indices of the type of a term in the type of other terms is
systematically supported.

Regarding the high-level specification language, Pierre Boutillier
introduced the ability to give implicit arguments to anonymous
functions, Hugo Herbelin introduced the ability to define notations with
several binders (e.g. ``exists x y z, P``), Matthieu Sozeau made the
typeclass inference mechanism more robust and predictable, Enrico
Tassi introduced a command Arguments that generalizes Implicit Arguments
and Arguments Scope for assigning various properties to arguments of
constants. Various improvements in the type inference algorithm were
provided by Matthieu Sozeau and Hugo Herbelin with contributions from
Enrico Tassi.

Regarding tactics, Hugo Herbelin introduced support for referring to
expressions occurring in the goal by pattern in tactics such as set or
destruct. Hugo Herbelin also relied on ideas from Chung-Kil Hur’s Heq
plugin to introduce automatic computation of occurrences to generalize
when using destruct and induction on types with indices. Stéphane Glondu
introduced new tactics :tacn:`constr_eq`, :tacn:`is_evar`, and :tacn:`has_evar`, to be used
when writing complex tactics. Enrico Tassi added support to fine-tuning
the behavior of :tacn:`simpl`. Enrico Tassi added the ability to specify over
which variables of a section a lemma has to be exactly generalized.
Pierre Letouzey added a tactic timeout and the interruptibility of
:tacn:`vm_compute`. Bug fixes and miscellaneous improvements of the tactic
language came from Hugo Herbelin, Pierre Letouzey and Matthieu Sozeau.

Regarding decision tactics, Loïc Pottier maintained nsatz, moving in
particular to a typeclass based reification of goals while Frédéric
Besson maintained Micromega, adding in particular support for division.

Regarding vernacular commands, Stéphane Glondu provided new commands to
analyze the structure of type universes.

Regarding libraries, a new library about lists of a given length (called
vectors) has been provided by Pierre Boutillier. A new instance of
finite sets based on Red-Black trees and provided by Andrew Appel has
been adapted for the standard library by Pierre Letouzey. In the library
of real analysis, Yves Bertot changed the definition of :math:`\pi` and
provided a proof of the long-standing fact yet remaining unproved in
this library, namely that :math:`sin \frac{\pi}{2} =
1`.

Pierre Corbineau maintained the Mathematical Proof Language (C-zar).

Bruno Barras and Benjamin Grégoire maintained the call-by-value
reduction machines.

The extraction mechanism benefited from several improvements provided by
Pierre Letouzey.

Pierre Letouzey maintained the module system, with contributions from
Élie Soubiran.

Julien Forest maintained the Function command.

Matthieu Sozeau maintained the setoid rewriting mechanism.

Coq related tools have been upgraded too. In particular, coq\_makefile
has been largely revised by Pierre Boutillier. Also, patches from Adam
Chlipala for coqdoc have been integrated by Pierre Boutillier.

Bruno Barras and Pierre Letouzey maintained the `coqchk` checker.

Pierre Courtieu and Arnaud Spiwack contributed new features for using
Coq through Proof General.

The Dp plugin has been removed. Use the plugin provided with Why 3
instead (http://why3.lri.fr/).

Under the hood, the |Coq| architecture benefited from improvements in
terms of efficiency and robustness, especially regarding universes
management and existential variables management, thanks to Pierre
Letouzey and Yann Régis-Gianas with contributions from Stéphane Glondu
and Matthias Puech. The build system is maintained by Pierre Letouzey
with contributions from Stéphane Glondu and Pierre Boutillier.

A new backtracking mechanism simplifying the task of external interfaces
has been designed by Pierre Letouzey.

The general maintenance was done by Pierre Letouzey, Hugo Herbelin,
Pierre Boutillier, Matthieu Sozeau and Stéphane Glondu with also
specific contributions from Guillaume Melquiond, Julien Narboux and
Pierre-Marie Pédrot.

Packaging tools were provided by Pierre Letouzey (Windows), Pierre
Boutillier (MacOS), Stéphane Glondu (Debian). Releasing, testing and
benchmarking support was provided by Jean-Marc Notin.

Many suggestions for improvements were motivated by feedback from users,
on either the bug tracker or the Coq-Club mailing list. Special thanks
are going to the users who contributed patches, starting with Tom
Prince. Other patch contributors include Cédric Auger, David Baelde, Dan
Grayson, Paolo Herms, Robbert Krebbers, Marc Lasson, Hendrik Tews and
Eelis van der Weegen.

| Paris, December 2011
| Hugo Herbelin
|

Potential sources of incompatibilities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The main known incompatibilities between 8.3 and 8.4 are consequences
of the following changes:

- The reorganization of the library of numbers:

  Several definitions have new names or are defined in modules of
  different names, but a special care has been taken to have this
  renaming transparent for the user thanks to compatibility notations.

  However some definitions have changed, what might require some
  adaptations. The most noticeable examples are:

  + The "?=" notation which now bind to Pos.compare rather than former
    Pcompare (now Pos.compare_cont).
  + Changes in names may induce different automatically generated
    names in proof scripts (e.g. when issuing "destruct Z_le_gt_dec").
  + Z.add has a new definition, hence, applying "simpl" on subterms of
    its body might give different results than before.
  + BigN.shiftl and BigN.shiftr have reversed arguments order, the
    power function in BigN now takes two BigN.

- Other changes in libraries:

  + The definition of functions over "vectors" (list of fixed length)
    have changed.
  + TheoryList.v has been removed.

- Slight changes in tactics:

  + Less unfolding of fixpoints when applying destruct or inversion on
    a fixpoint hiding an inductive type (add an extra call to simpl to
    preserve compatibility).
  + Less unexpected local definitions when applying "destruct"
    (incompatibilities solvable by adapting name hypotheses).
  + Tactic "apply" might succeed more often, e.g. by now solving
    pattern-matching of the form ?f x y = g(x,y) (compatibility
    ensured by using "Unset Tactic Pattern Unification"), but also
    because it supports (full) betaiota (using "simple apply" might
    then help).
  + Tactic autorewrite does no longer instantiate pre-existing
    existential variables.
  + Tactic "info" is now available only for auto, eauto and trivial.

- Miscellaneous changes:

  + The command "Load" is now atomic for backtracking (use "Unset
    Atomic Load" for compatibility).

Details of changes in 8.4beta
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Logic

- Standard eta-conversion now supported (dependent product only).
- Guard condition improvement: subterm property is propagated through beta-redex
  blocked by pattern-matching, as in "(match v with C .. => fun x => u end) x";
  this allows for instance to use "rewrite ... in ..." without breaking
  the guard condition.

Specification language and notations

- Maximal implicit arguments can now be set locally by { }. The registration
  traverses fixpoints and lambdas. Because there is conversion in types,
  maximal implicit arguments are not taken into account in partial
  applications (use eta expanded form with explicit { } instead).
- Added support for recursive notations with binders (allows for instance
  to write "exists x y z, P").
- Structure/Record printing can be disable by "Unset Printing Records".
  In addition, it can be controlled on type by type basis using
  "Add Printing Record" or "Add Printing Constructor".
- Pattern-matching compilation algorithm: in "match x, y with ... end",
  possible dependencies of x (or of the indices of its type) in the type
  of y are now taken into account.

Tactics

- New proof engine.
- Scripts can now be structured thanks to bullets - * + and to subgoal
  delimitation via { }. Note: for use with Proof General, a cvs version of
  Proof General no older than mid-July 2011 is currently required.
- Support for tactical "info" is suspended.
- Support for command "Show Script" is suspended.
- New tactics constr_eq, is_evar and has_evar for use in Ltac (DOC TODO).
- Removed the two-argument variant of "decide equality".
- New experimental tactical "timeout <n> <tac>". Since <n> is a time
  in second for the moment, this feature should rather be avoided
  in scripts meant to be machine-independent.
- Fix in "destruct": removal of unexpected local definitions in context might
  result in some rare incompatibilities (solvable by adapting name hypotheses).
- Introduction pattern "_" made more robust.
- Tactic (and Eval command) vm_compute can now be interrupted via Ctrl-C.
- Unification in "apply" supports unification of patterns of the form
  ?f x y = g(x,y) (compatibility ensured by using
  "Unset Tactic Pattern Unification"). It also supports (full) betaiota.
- Tactic autorewrite does no longer instantiate pre-existing
  existential variables (theoretical source of possible incompatibilities).
- Tactic "dependent rewrite" now supports equality in "sig".
- Tactic omega now understands Zpred (wish #1912) and can prove any goal
  from a context containing an arithmetical contradiction (wish #2236).
- Using "auto with nocore" disables the use of the "core" database (wish #2188).
  This pseudo-database "nocore" can also be used with trivial and eauto.
- Tactics "set", "destruct" and "induction" accepts incomplete terms and
  use the goal to complete the pattern assuming it is non ambiguous.
- When used on arguments with a dependent type, tactics such as
  "destruct", "induction", "case", "elim", etc. now try to abstract
  automatically the dependencies over the arguments of the types
  (based on initial ideas from Chung-Kil Hur, extension to nested
  dependencies suggested by Dan Grayson)
- Tactic "injection" now failing on an equality showing no constructors while
  it was formerly generalizing again the goal over the given equality.
- In Ltac, the "context [...]" syntax has now a variant "appcontext [...]"
  allowing to match partial applications in larger applications.
- When applying destruct or inversion on a fixpoint hiding an inductive
  type, recursive calls to the fixpoint now remain folded by default (rare
  source of incompatibility generally solvable by adding a call to simpl).
- In an ltac pattern containing a "match", a final "| _ => _" branch could be
  used now instead of enumerating all remaining constructors. Moreover, the
  pattern "match _ with _ => _ end" now allows to match any "match". A "in"
  annotation can also be added to restrict to a precise inductive type.
- The behavior of "simpl" can be tuned using the "Arguments" vernacular.
  In particular constants can be marked so that they are always/never unfolded
  by "simpl", or unfolded only when a set of arguments evaluates to a
  constructor. Last one can mark a constant so that it is unfolded only if the
  simplified term does not expose a match in head position.

Vernacular commands

- It is now mandatory to have a space (or tabulation or newline or end-of-file)
  after a "." ending a sentence.
- In SearchAbout, the [ ] delimiters are now optional.
- New command "Add/Remove Search Blacklist <substring> ...":
  a Search or SearchAbout or similar query will never mention lemmas
  whose qualified names contain any of the declared substrings.
  The default blacklisted substrings are ``_subproof``, ``Private_``.
- When the output file of "Print Universes" ends in ".dot" or ".gv",
  the universe graph is printed in the DOT language, and can be
  processed by Graphviz tools.
- New command "Print Sorted Universes".
- The undocumented and obsolete option "Set/Unset Boxed Definitions" has
  been removed, as well as syntaxes like "Boxed Fixpoint foo".
- A new option "Set Default Timeout n / Unset Default Timeout".
- Qed now uses information from the reduction tactics used in proof script
  to avoid conversion at Qed time to go into a very long computation.
- New command "Show Goal ident" to display the statement of a goal, even
  a closed one (available from Proof General).
- Command "Proof" accept a new modifier "using" to force generalization
  over a given list of section variables at section ending (DOC TODO).
- New command "Arguments" generalizing "Implicit Arguments" and
  "Arguments Scope" and that also allows to rename the parameters of a
  definition and to tune the behavior of the tactic "simpl".

Module System

- During subtyping checks, an opaque constant in a module type could now
  be implemented by anything of the right type, even if bodies differ.
  Said otherwise, with respect to subtyping, an opaque constant behaves
  just as a parameter. Coqchk was already implementing this, but not coqtop.
- The inlining done during application of functors can now be controlled
  more precisely, by the annotations (no inline) or (inline at level XX).
  With the latter annotation, only functor parameters whose levels
  are lower or equal than XX will be inlined.
  The level of a parameter can be fixed by "Parameter Inline(30) foo".
  When levels aren't given, the default value is 100. One can also use
  the flag "Set Inline Level ..." to set a level (DOC TODO).
- Print Assumptions should now handle correctly opaque modules (#2168).
- Print Module (Type) now tries to print more details, such as types and
  bodies of the module elements. Note that Print Module Type could be
  used on a module to display only its interface. The option
  "Set Short Module Printing" could be used to switch back to the earlier
  behavior were only field names were displayed.

Libraries

- Extension of the abstract part of Numbers, which now provide axiomatizations
  and results about many more integer functions, such as pow, gcd, lcm, sqrt,
  log2 and bitwise functions. These functions are implemented for nat, N, BigN,
  Z, BigZ. See in particular file NPeano for new functions about nat.

- The definition of types positive, N, Z is now in file BinNums.v

- Major reorganization of ZArith. The initial file ZArith/BinInt.v now contains
  an internal module Z implementing the Numbers interface for integers.
  This module Z regroups:

  * all functions over type Z : Z.add, Z.mul, ...
  * the minimal proofs of specifications for these functions : Z.add_0_l, ...
  * an instantiation of all derived properties proved generically in Numbers :
    Z.add_comm, Z.add_assoc, ...

  A large part of ZArith is now simply compatibility notations, for instance
  Zplus_comm is an alias for Z.add_comm. The direct use of module Z is now
  recommended instead of relying on these compatibility notations.

- Similar major reorganization of NArith, via a module N in NArith/BinNat.v

- Concerning the positive datatype, BinPos.v is now in a specific directory
  PArith, and contains an internal submodule Pos. We regroup there functions
  such as Pos.add Pos.mul etc as well as many results about them. These results
  are here proved directly (no Number interface for strictly positive numbers).

- Note that in spite of the compatibility layers, all these reorganizations
  may induce some marginal incompatibilies in scripts. In particular:

  * the "?=" notation for positive now refers to a binary function Pos.compare,
    instead of the infamous ternary Pcompare (now Pos.compare_cont).
  * some hypothesis names generated by the system may changed (typically for
    a "destruct Z_le_gt_dec") since naming is done after the short name of
    the head predicate (here now "le" in module Z instead of "Zle", etc).
  * the internals of Z.add has changed, now relying of Z.pos_sub.

- Also note these new notations:

  * "<?" "<=?" "=?" for boolean tests such as Z.ltb Z.leb Z.eqb.
  * "÷" for the alternative integer division Z.quot implementing the Truncate
    convention (former ZOdiv), while the notation for the Coq usual division
    Z.div implementing the Flooring convention remains "/". Their corresponding
    modulo functions are Z.rem (no notations) for Z.quot and Z.modulo (infix
    "mod" notation) for Z.div.

- Lemmas about conversions between these datatypes are also organized
  in modules, see for instance modules Z2Nat, N2Z, etc.

- When creating BigN, the macro-generated part NMake_gen is much smaller.
  The generic part NMake has been reworked and improved. Some changes
  may introduce incompatibilities. In particular, the order of the arguments
  for BigN.shiftl and BigN.shiftr is now reversed: the number to shift now
  comes first. By default, the power function now takes two BigN.

- Creation of Vector, an independent library for lists indexed by their length.
  Vectors' names overwrite lists' one so you should not "Import" the library.
  All old names changed: function names follow the ocaml ones and, for example,
  Vcons becomes Vector.cons. You can get [..;..;..]-style notations by importing
  Vector.VectorNotations.

- Removal of TheoryList. Requiring List instead should work most of the time.

- New syntax "rew Heq in H" and "rew <- Heq in H" for eq_rect and
  eq_rect_r (available by importing module EqNotations).

- Wf.iter_nat is now Peano.nat_iter (with an implicit type argument).

Internal infrastructure

- Opaque proofs are now loaded lazily by default. This allows to be almost as
  fast as -dont-load-proofs, while being safer (no creation of axioms) and
  avoiding feature restrictions (Print and Print Assumptions work ok).
- Revised hash-consing code allowing more sharing of memory
- Experimental support added for camlp4 (the one provided alongside ocaml),
  simply pass option -usecamlp4 to ./configure. By default camlp5 is used.
- Revised build system: no more stages in Makefile thanks to some recursive
  aspect of recent gnu make, use of vo.itarget files containing .v to compile
  for both make and ocamlbuild, etc.
- Support of cross-compilation via mingw from unix toward Windows,
  contact P. Letouzey for more informations.
- New Makefile rules mli-doc to make html of mli in dev/doc/html and
  full-stdlib to get a (huge) pdf reflecting the whole standard library.

Extraction

- By default, opaque terms are now truly considered opaque by extraction:
  instead of accessing their body, they are now considered as axioms.
  The previous behaviour can be reactivated via the option
  "Set Extraction AccessOpaque".
- The pretty-printer for Haskell now produces layout-independent code
- A new command "Separate Extraction cst1 cst2 ..." that mixes a
  minimal extracted environment a la "Recursive Extraction" and the
  production of several files (one per coq source) a la "Extraction Library"
  (DOC TODO).
- New option "Set/Unset Extraction KeepSingleton" for preventing the
  extraction to optimize singleton container types (DOC TODO).
- The extraction now identifies and properly rejects a particular case of
  universe polymorphism it cannot handle yet (the pair (I,I) being Prop).
- Support of anonymous fields in record (#2555).

CoqIDE

- Coqide now runs coqtop as separated process, making it more robust:
  coqtop subprocess can be interrupted, or even killed and relaunched
  (cf button "Restart Coq", ex-"Go to Start"). For allowing such
  interrupts, the Windows version of coqide now requires Windows >= XP
  SP1.
- The communication between CoqIDE and Coqtop is now done via a dialect
  of XML (DOC TODO).
- The backtrack engine of CoqIDE has been reworked, it now uses the
  "Backtrack" command similarly to Proof General.
- The Coqide parsing of sentences has be reworked and now supports
  tactic delimitation via { }.
- Coqide now accepts the Abort command (wish #2357).
- Coqide can read coq_makefile files as "project file" and use it to
  set automatically options to send to coqtop.
- Preference files have moved to $XDG_CONFIG_HOME/coq and accelerators
  are not stored as a list anymore.

Tools

- Coq now searches directories specified in COQPATH, $XDG_DATA_HOME/coq,
  $XDG_DATA_DIRS/coq, and user-contribs before the standard library.

- Coq rc file has moved to $XDG_CONFIG_HOME/coq.

- Major changes to coq_makefile:

  * mli/mlpack/mllib taken into account, ml not preproccessed anymore, ml4 work;
  * mlihtml generates doc of mli, install-doc install the html doc in DOCDIR
    with the same policy as vo in COQLIB;
  * More variables are given by coqtop -config, others are defined only if the
    users doesn't have defined them elsewhere. Consequently, generated makefile
    should work directly on any architecture;
  * Packagers can take advantage of $(DSTROOT) introduction. Installation can
    be made in $XDG_DATA_HOME/coq;
  * -arg option allows to send option as argument to coqc.

Details of changes in 8.4beta2
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Vernacular commands

- Commands "Back" and "BackTo" are now handling the proof states. They may
  perform some extra steps of backtrack to avoid states where the proof
  state is unavailable (typically a closed proof).
- The commands "Suspend" and "Resume" have been removed.
- A basic Show Script has been reintroduced (no indentation).
- New command "Set Parsing Explicit" for deactivating parsing (and printing)
  of implicit arguments (useful for teaching).
- New command "Grab Existential Variables" to transform the unresolved evars
  at the end of a proof into goals.

Tactics

- Still no general "info" tactical, but new specific tactics info_auto,
  info_eauto, info_trivial which provides information on the proofs found
  by auto/eauto/trivial. Display of these details could also be activated by
  "Set Info Auto"/"Set Info Eauto"/"Set Info Trivial".
- Details on everything tried by auto/eauto/trivial during a proof search
  could be obtained by "debug auto", "debug eauto", "debug trivial" or by a
  global "Set Debug Auto"/"Set Debug Eauto"/"Set Debug Trivial".
- New command "r string" in Ltac debugger that interprets "idtac
  string" in Ltac code as a breakpoint and jumps to its next use.
- Tactics from the Dp plugin (simplify, ergo, yices, cvc3, z3, cvcl,
  harvey, zenon, gwhy) have been removed, since Why2 has not been
  maintained for the last few years. The Why3 plugin should be a suitable
  replacement in most cases.

Libraries

- MSetRBT: a new implementation of MSets via Red-Black trees (initial
  contribution by Andrew Appel).
- MSetAVL: for maximal sharing with the new MSetRBT, the argument order
  of Node has changed (this should be transparent to regular MSets users).

Module System

- The names of modules (and module types) are now in a fully separated
  namespace from ordinary definitions: "Definition E:=0. Module E. End E."
  is now accepted.

CoqIDE

- Coqide now supports the "Restart" command, and "Undo" (with a warning).
  Better support for "Abort".

Details of changes in 8.4
~~~~~~~~~~~~~~~~~~~~~~~~~

Vernacular commands

- The "Reset" command is now supported again in files given to coqc or Load.
- "Show Script" now indents again the displayed scripts. It can also work
  correctly across Load'ed files if the option "Unset Atomic Load" is used.
- "Open Scope" can now be given the delimiter (e.g. Z) instead of the full
  scope name (e.g. Z_scope).

Notations

- Most compatibility notations of the standard library are now tagged as
  (compat xyz), where xyz is a former Coq version, for instance "8.3".
  These notations behave as (only parsing) notations, except that they may
  triggers warnings (or errors) when used while Coq is not in a corresponding
  -compat mode.
- To activate these compatibility warnings, use "Set Verbose Compat Notations"
  or the command-line flag -verbose-compat-notations.
- For a strict mode without these compatibility notations, use
  "Unset Compat Notations" or the command-line flag -no-compat-notations.

Tactics

- An annotation "eqn:H" or "eqn:?" can be added to a "destruct"
  or "induction" to make it generate equations in the spirit of "case_eq".
  The former syntax "_eqn" is discontinued.
- The name of the hypothesis introduced by tactic "remember" can be
  set via the new syntax "remember t as x eqn:H" (wish #2489).

Libraries

- Reals: changed definition of PI, no more axiom about sin(PI/2).
- SetoidPermutation: a notion of permutation for lists modulo a setoid equality.
- BigN: fixed the ocaml code doing the parsing/printing of big numbers.
- List: a couple of lemmas added especially about no-duplication, partitions.
- Init: Removal of the coercions between variants of sigma-types and
  subset types (possible source of incompatibility).

Version 8.3
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

Coq version 8.3 is before all a transition version with refinements or
extensions of the existing features and libraries and a new tactic nsatz
based on Hilbert’s Nullstellensatz for deciding systems of equations
over rings.

With respect to libraries, the main evolutions are due to Pierre
Letouzey with a rewriting of the library of finite sets FSets and a new
round of evolutions in the modular development of arithmetic (library
Numbers). The reason for making FSets evolve is that the computational
and logical contents were quite intertwined in the original
implementation, leading in some cases to longer computations than
expected and this problem is solved in the new MSets implementation. As
for the modular arithmetic library, it was only dealing with the basic
arithmetic operators in the former version and its current extension
adds the standard theory of the division, min and max functions, all
made available for free to any implementation of :math:`\mathbb{N}`,
:math:`\mathbb{Z}` or :math:`\mathbb{Z}/n\mathbb{Z}`.

The main other evolutions of the library are due to Hugo Herbelin who
made a revision of the sorting library (including a certified
merge-sort) and to Guillaume Melquiond who slightly revised and cleaned
up the library of reals.

The module system evolved significantly. Besides the resolution of some
efficiency issues and a more flexible construction of module types, Élie
Soubiran brought a new model of name equivalence, the
:math:`\Delta`-equivalence, which respects as much as possible the names
given by the users. He also designed with Pierre Letouzey a new,
convenient operator ``<+`` for nesting functor application that
provides a light notation for inheriting the properties of cascading
modules.

The new tactic nsatz is due to Loïc Pottier. It works by computing
Gröbner bases. Regarding the existing tactics, various improvements have
been done by Matthieu Sozeau, Hugo Herbelin and Pierre Letouzey.

Matthieu Sozeau extended and refined the typeclasses and Program
features (the Russell language). Pierre Letouzey maintained and improved
the extraction mechanism. Bruno Barras and Élie Soubiran maintained the
Coq checker, Julien Forest maintained the Function mechanism for
reasoning over recursively defined functions. Matthieu Sozeau, Hugo
Herbelin and Jean-Marc Notin maintained coqdoc. Frédéric Besson
maintained the Micromega platform for deciding systems of inequalities.
Pierre Courtieu maintained the support for the Proof General Emacs
interface. Claude Marché maintained the plugin for calling external
provers (dp). Yves Bertot made some improvements to the libraries of
lists and integers. Matthias Puech improved the search functions.
Guillaume Melquiond usefully contributed here and there. Yann
Régis-Gianas grounded the support for Unicode on a more standard and
more robust basis.

Though invisible from outside, Arnaud Spiwack improved the general
process of management of existential variables. Pierre Letouzey and
Stéphane Glondu improved the compilation scheme of the |Coq| archive.
Vincent Gross provided support to |CoqIDE|. Jean-Marc Notin provided
support for benchmarking and archiving.

Many users helped by reporting problems, providing patches, suggesting
improvements or making useful comments, either on the bug tracker or on
the Coq-Club mailing list. This includes but not exhaustively Cédric
Auger, Arthur Charguéraud, François Garillot, Georges Gonthier, Robin
Green, Stéphane Lescuyer, Eelis van der Weegen, ...

Though not directly related to the implementation, special thanks are
going to Yves Bertot, Pierre Castéran, Adam Chlipala, and Benjamin
Pierce for the excellent teaching materials they provided.

| Paris, April 2010
| Hugo Herbelin
|

Details of changes
~~~~~~~~~~~~~~~~~~

Rewriting tactics

- Tactic "rewrite" now supports rewriting on ad hoc equalities such as eq_true.
- "Hint Rewrite" now checks that the lemma looks like an equation.
- New tactic "etransitivity".
- Support for heterogeneous equality (JMeq) in "injection" and "discriminate".
- Tactic "subst" now supports heterogeneous equality and equality
  proofs that are dependent (use "simple subst" for preserving compatibility).
- Added support for Leibniz-rewriting of dependent hypotheses.
- Renamed "Morphism" into "Proper" and "respect" into "proper_prf"
  (possible source of incompatibility). A partial fix is to define
  "Notation Morphism R f := (Proper (R%signature) f)."
- New tactic variants "rewrite* by" and "autorewrite*" that rewrite
  respectively the first and all matches whose side-conditions are
  solved.
- "Require Import Setoid" does not export all of "Morphisms" and
  "RelationClasses" anymore (possible source of incompatibility, fixed
  by importing "Morphisms" too).
- Support added for using Chung-Kil Hur's Heq library for rewriting over
  heterogeneous equality (courtesy of the library's author).
- Tactic "replace" supports matching terms with holes.

Automation tactics

- Tactic ``intuition`` now preserves inner ``iff`` and ``not`` (exceptional
  source of incompatibilities solvable by redefining ``intuition`` as
  ``unfold iff, not in *; intuition``, or, for iff only, by using
  ``Set Intuition Iff Unfolding``.)
- Tactic ``tauto`` now proves classical tautologies as soon as classical logic
  (i.e. library ``Classical_Prop`` or ``Classical``) is loaded.
- Tactic ``gappa`` has been removed from the Dp plugin.
- Tactic ``firstorder`` now supports the combination of its ``using`` and
  ``with`` options.
- New ``Hint Resolve ->`` (or ``<-``) for declaring iff's as oriented
  hints (wish #2104).
- An inductive type as argument of the ``using`` option of ``auto`` / ``eauto`` / ``firstorder``
  is interpreted as using the collection of its constructors.
- New decision tactic "nsatz" to prove polynomial equations
  by computation of Groebner bases.

Other tactics

- Tactic "discriminate" now performs intros before trying to discriminate an
  hypothesis of the goal (previously it applied intro only if the goal
  had the form t1<>t2) (exceptional source of incompatibilities - former
  behavior can be obtained by "Unset Discriminate Introduction").
- Tactic "quote" now supports quotation of arbitrary terms (not just the
  goal).
- Tactic "idtac" now displays its "list" arguments.
- New introduction patterns "*" for introducing the next block of dependent
  variables and "**" for introducing all quantified variables and hypotheses.
- Pattern Unification for existential variables activated in tactics and
  new option "Unset Tactic Evars Pattern Unification" to deactivate it.
- Resolution of canonical structure is now part of the tactic's unification
  algorithm.
- New tactic "decide lemma with hyp" for rewriting decidability lemmas
  when one knows which side is true.
- Improved support of dependent goals over objects in dependent types for
  "destruct" (rare source of incompatibility that can be avoided by unsetting
  option "Dependent Propositions Elimination").
- Tactic "exists", "eexists", "destruct" and "edestruct" supports iteration
  using comma-separated arguments.
- Tactic names "case" and "elim" now support clauses "as" and "in" and become
  then synonymous of "destruct" and "induction" respectively.
- A new tactic name "exfalso" for the use of 'ex-falso quodlibet' principle.
  This tactic is simply a shortcut for "elimtype False".
- Made quantified hypotheses get the name they would have if introduced in
  the context (possible but rare source of incompatibilities).
- When applying a component of a conjunctive lemma, "apply in" (and
  sequences of "apply in") now leave the side conditions of the lemmas
  uniformly after the main goal (possible source of rare incompatibilities).
- In "simpl c" and "change c with d", c can be a pattern.
- Tactic "revert" now preserves let-in's making it the exact inverse of
  "intro".
- New tactics "clear dependent H" and "revert dependent H" that
  clears (resp. reverts) H and all the hypotheses that depend on H.
- Ltac's pattern-matching now supports matching metavariables that
  depend on variables bound upwards in the pattern.

Tactic definitions

- Ltac definitions support Local option for non-export outside modules.
- Support for parsing non-empty lists with separators in tactic notations.
- New command "Locate Ltac" to get the full name of an Ltac definition.

Notations

- Record syntax ``{|x=...; y=...|}`` now works inside patterns too.
- Abbreviations from non-imported module now invisible at printing time.
- Abbreviations now use implicit arguments and arguments scopes for printing.
- Abbreviations to pure names now strictly behave like the name they refer to
  (make redirections of qualified names easier).
- Abbreviations for applied constant now propagate the implicit arguments
  and arguments scope of the underlying reference (possible source of
  incompatibilities generally solvable by changing such abbreviations from
  e.g. ``Notation foo' := (foo x)`` to ``Notation foo' y := (foo x (y:=y))``).
- The "where" clause now supports multiple notations per defined object.
- Recursive notations automatically expand one step on the left for better
  factorization; recursion notations inner separators now ensured being tokens.
- Added "Reserved Infix" as a specific shortcut of the corresponding
  "Reserved Notation".
- Open/Close Scope command supports Global option in sections.

Specification language

- New support for local binders in the syntax of Record/Structure fields.
- Fixpoint/CoFixpoint now support building part or all of bodies using tactics.
- Binders given before ":" in lemmas and in definitions built by tactics are
  now automatically introduced (possible source of incompatibility that can
  be resolved by invoking "Unset Automatic Introduction").
- New support for multiple implicit arguments signatures per reference.

Module system

- Include Type is now deprecated since Include now accept both modules and
  module types.
- Declare ML Module supports Local option.
- The sharing between non-logical object and the management of the
  name-space has been improved by the new "Delta-equivalence" on
  qualified name.
- The include operator has been extended to high-order structures
- Sequences of Include can be abbreviated via new syntax "<+".
- A module (or module type) can be given several "<:" signatures.
- Interactive proofs are now permitted in module type. Functors can hence
  be declared as Module Type and be used later to type themselves.
- A functor application can be prefixed by a "!" to make it ignore any
  "Inline" annotation in the type of its argument(s) (for examples of
  use of the new features, see libraries Structures and Numbers).
- Coercions are now active only when modules are imported (use "Set Automatic
  Coercions Import" to get the behavior of the previous versions of Coq).

Extraction

- When using (Recursive) Extraction Library, the filenames are directly the
  Coq ones with new appropriate extensions : we do not force anymore
  uncapital first letters for Ocaml and capital ones for Haskell.
- The extraction now tries harder to avoid code transformations that can be
  dangerous for the complexity. In particular many eta-expansions at the top
  of functions body are now avoided, clever partial applications will likely
  be preserved, let-ins are almost always kept, etc.
- In the same spirit, auto-inlining is now disabled by default, except for
  induction principles, since this feature was producing more frequently
  weird code than clear gain. The previous behavior can be restored via
  "Set Extraction AutoInline".
- Unicode characters in identifiers are now transformed into ascii strings
  that are legal in Ocaml and other languages.
- Harsh support of module extraction to Haskell and Scheme: module hierarchy
  is flattened, module abbreviations and functor applications are expanded,
  module types and unapplied functors are discarded.
- Less unsupported situations when extracting modules to Ocaml. In particular
  module parameters might be alpha-renamed if a name clash is detected.
- Extract Inductive is now possible toward non-inductive types (e.g. nat => int)
- Extraction Implicit: this new experimental command allows to mark
  some arguments of a function or constructor for removed during
  extraction, even if these arguments don't fit the usual elimination
  principles of extraction, for instance the length n of a vector.
- Files ExtrOcaml*.v in plugins/extraction try to provide a library of common
  extraction commands: mapping of basics types toward Ocaml's counterparts,
  conversions from/to int and big_int, or even complete mapping of nat,Z,N
  to int or big_int, or mapping of ascii to char and string to char list
  (in this case recognition of ascii constants is hard-wired in the extraction).

Program

- Streamlined definitions using well-founded recursion and measures so
  that they can work on any subset of the arguments directly (uses currying).
- Try to automatically clear structural fixpoint prototypes in
  obligations to avoid issues with opacity.
- Use return type clause inference in pattern-matching as in the standard
  typing algorithm.
- Support [Local Obligation Tactic] and [Next Obligation with tactic].
- Use [Show Obligation Tactic] to print the current default tactic.
- [fst] and [snd] have maximal implicit arguments in Program now (possible
  source of incompatibility).

Type classes

- Declaring axiomatic type class instances in Module Type should be now
  done via new command "Declare Instance", while the syntax "Instance"
  now always provides a concrete instance, both in and out of Module Type.
- Use [Existing Class foo] to declare foo as a class a posteriori.
  [foo] can be an inductive type or a constant definition. No
  projections or instances are defined.
- Various bug fixes and improvements: support for defined fields,
  anonymous instances, declarations giving terms, better handling of
  sections and [Context].

Vernacular commands

- New command "Timeout <n> <command>." interprets a command and a timeout
  interrupts the interpretation after <n> seconds.
- New command "Compute <expr>." is a shortcut for "Eval vm_compute in <expr>".
- New command "Fail <command>." interprets a command and is successful iff
  the command fails on an error (but not an anomaly). Handy for tests and
  illustration of wrong commands.
- Most commands referring to constant (e.g. Print or About) now support
  referring to the constant by a notation string.
- New option "Boolean Equality Schemes" to make generation of boolean
  equality automatic for datatypes (together with option "Decidable
  Equality Schemes", this replaces deprecated option "Equality Scheme").
- Made support for automatic generation of case analysis schemes available
  to user (governed by option "Set Case Analysis Schemes").
- New command :n:`{? Global } Generalizable {| All | No } {| Variable | Variables } {* @ident}` to
  declare which identifiers are generalizable in `` `{} `` and `` `() `` binders.
- New command "Print Opaque Dependencies" to display opaque constants in
  addition to all variables, parameters or axioms a theorem or
  definition relies on.
- New command "Declare Reduction <id> := <conv_expr>", allowing to write
  later "Eval <id> in ...". This command accepts a Local variant.
- Syntax of Implicit Type now supports more than one block of variables of
  a given type.
- Command "Canonical Structure" now warns when it has no effects.
- Commands of the form "Set X" or "Unset X" now support "Local" and "Global"
  prefixes.

Library

- Use "standard" Coq names for the properties of eq and identity
  (e.g. refl_equal is now eq_refl). Support for compatibility is provided.

- The function Compare_dec.nat_compare is now defined directly,
  instead of relying on lt_eq_lt_dec. The earlier version is still
  available under the name nat_compare_alt.

- Lemmas in library Relations and Reals have been homogenized a bit.

- The implicit argument of Logic.eq is now maximally inserted, allowing
  to simply write "eq" instead of "@eq _" in morphism signatures.

- Wrongly named lemmas (Zlt_gt_succ and Zlt_succ_gt) fixed (potential source
  of incompatibilities)

- List library:

  + Definitions of list, length and app are now in Init/Datatypes.
    Support for compatibility is provided.
  + Definition of Permutation is now in Sorting/Permtation.v
  + Some other light revisions and extensions (possible source
    of incompatibilities solvable by qualifying names accordingly).

- In ListSet, set_map has been fixed (source of incompatibilities if used).

- Sorting library:

  + new mergesort of worst-case complexity O(n*ln(n)) made available in
    Mergesort.v;
  + former notion of permutation up to setoid from Permutation.v is
    deprecated and moved to PermutSetoid.v;
  + heapsort from Heap.v of worst-case complexity O(n*n) is deprecated;
  + new file Sorted.v for some definitions of being sorted.

- Structure library. This new library is meant to contain generic
  structures such as types with equalities or orders, either
  in Module version (for now) or Type Classes (still to do):

  + DecidableType.v and OrderedType.v: initial notions for FSets/FMaps,
    left for compatibility but considered as deprecated.
  + Equalities.v and Orders.v: evolutions of the previous files,
    with fine-grain Module architecture, many variants, use of
    Equivalence and other relevant Type Classes notions.
  + OrdersTac.v: a generic tactic for solving chains of (in)equalities
    over variables. See {Nat,N,Z,P}OrderedType.v for concrete instances.
  + GenericMinMax.v: any ordered type can be equipped with min and max.
    We derived here all the generic properties of these functions.

- MSets library: an important evolution of the FSets library.
  "MSets" stands for Modular (Finite) Sets, by contrast with a forthcoming
  library of Class (Finite) Sets contributed by S. Lescuyer which will be
  integrated with the next release of Coq. The main features of MSets are:

  + The use of Equivalence, Proper and other Type Classes features
    easing the handling of setoid equalities.
  + The interfaces are now stated in iff-style. Old specifications
    are now derived properties.
  + The compare functions are now pure, and return a "comparison" value.
    Thanks to the CompSpec inductive type, reasoning on them remains easy.
  + Sets structures requiring invariants (i.e. sorted lists) are
    built first as "Raw" sets (pure objects and separate proofs) and
    attached with their proofs thanks to a generic functor. "Raw" sets
    have now a proper interface and can be manipulated directly.

  Note: No Maps yet in MSets. The FSets library is still provided
  for compatibility, but will probably be considered as deprecated in the
  next release of Coq.

- Numbers library:

  + The abstract layer (NatInt, Natural/Abstract, Integer/Abstract) has
    been simplified and enhance thanks to new features of the module
    system such as Include (see above). It has been extended to Euclidean
    division (three flavors for integers: Trunc, Floor and Math).
  + The arbitrary-large efficient numbers (BigN, BigZ, BigQ) has also
    been reworked. They benefit from the abstract layer improvements
    (especially for div and mod). Note that some specifications have
    slightly changed (compare, div, mod, shift{r,l}). Ring/Field should
    work better (true recognition of constants).

Tools

- Option -R now supports binding Coq root read-only.
- New coqtop/coqc option -beautify to reformat .v files (usable
  e.g. to globally update notations).
- New tool beautify-archive to beautify a full archive of developments.
- New coqtop/coqc option -compat X.Y to simulate the general behavior
  of previous versions of Coq (provides e.g. support for 8.2 compatibility).

Coqdoc

- List have been revamped.  List depth and scope is now determined by
  an "offside" whitespace rule.
- Text may be italicized by placing it in _underscores_.
- The "--index <string>" flag changes the filename of the index.
- The "--toc-depth <int>" flag limits the depth of headers which are
  included in the table of contents.
- The "--lib-name <string>" flag prints "<string> Foo" instead of
  "Library Foo" where library titles are called for.  The
  "--no-lib-name" flag eliminates the extra title.
- New option "--parse-comments" to allow parsing of regular ``(* *)``
  comments.
- New option "--plain-comments" to disable interpretation inside comments.
- New option "--interpolate" to try and typeset identifiers in Coq escapings
  using the available globalization information.
- New option "--external url root" to refer to external libraries.
- Links to section variables and notations now supported.

Internal infrastructure

- To avoid confusion with the repository of user's contributions,
  the subdirectory "contrib" has been renamed into "plugins".
  On platforms supporting ocaml native dynlink, code located there
  is built as loadable plugins for coqtop.
- An experimental build mechanism via ocamlbuild is provided.
  From the top of the archive, run ./configure as usual, and
  then ./build. Feedback about this build mechanism is most welcome.
  Compiling Coq on platforms such as Windows might be simpler
  this way, but this remains to be tested.
- The Makefile system has been simplified and factorized with
  the ocamlbuild system. In particular "make" takes advantage
  of .mllib files for building .cma/.cmxa. The .vo files to
  compile are now listed in several vo.itarget files.

Version 8.2
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

Coq version 8.2 adds new features, new libraries and improves on many
various aspects.

Regarding the language of |Coq|, the main novelty is the introduction by
Matthieu Sozeau of a package of commands providing Haskell-style typeclasses.
Typeclasses, which come with a few convenient features such as
type-based resolution of implicit arguments, play a new landmark role
in the architecture of |Coq| with respect to automation. For
instance, thanks to typeclass support, Matthieu Sozeau could
implement a new resolution-based version of the tactics dedicated to
rewriting on arbitrary transitive relations.

Another major improvement of |Coq| 8.2 is the evolution of the arithmetic
libraries and of the tools associated to them. Benjamin Grégoire and
Laurent Théry contributed a modular library for building arbitrarily
large integers from bounded integers while Evgeny Makarov contributed a
modular library of abstract natural and integer arithmetic together
with a few convenient tactics. On his side, Pierre Letouzey made
numerous extensions to the arithmetic libraries on :math:`\mathbb{Z}`
and :math:`\mathbb{Q}`, including extra support for automation in
presence of various number-theory concepts.

Frédéric Besson contributed a reflective tactic based on Krivine-Stengle
Positivstellensatz (the easy way) for validating provability of systems
of inequalities. The platform is flexible enough to support the
validation of any algorithm able to produce a “certificate” for the
Positivstellensatz and this covers the case of Fourier-Motzkin (for
linear systems in :math:`\mathbb{Q}` and :math:`\mathbb{R}`),
Fourier-Motzkin with cutting planes (for linear systems in
:math:`\mathbb{Z}`) and sum-of-squares (for non-linear systems). Evgeny
Makarov made the platform generic over arbitrary ordered rings.

Arnaud Spiwack developed a library of 31-bits machine integers and,
relying on Benjamin Grégoire and Laurent Théry’s library, delivered a
library of unbounded integers in base :math:`2^{31}`. As importantly, he
developed a notion of “retro-knowledge” so as to safely extend the
kernel-located bytecode-based efficient evaluation algorithm of |Coq|
version 8.1 to use 31-bits machine arithmetic for efficiently computing
with the library of integers he developed.

Beside the libraries, various improvements were contributed to provide a more
comfortable end-user language and more expressive tactic language. Hugo
Herbelin and Matthieu Sozeau improved the pattern matching compilation
algorithm (detection of impossible clauses in pattern matching,
automatic inference of the return type). Hugo Herbelin, Pierre Letouzey
and Matthieu Sozeau contributed various new convenient syntactic
constructs and new tactics or tactic features: more inference of
redundant information, better unification, better support for proof or
definition by fixpoint, more expressive rewriting tactics, better
support for meta-variables, more convenient notations...

Élie Soubiran improved the module system, adding new features (such as
an “include” command) and making it more flexible and more general. He
and Pierre Letouzey improved the support for modules in the extraction
mechanism.

Matthieu Sozeau extended the Russell language, ending in an convenient
way to write programs of given specifications, Pierre Corbineau extended
the Mathematical Proof Language and the automation tools that
accompany it, Pierre Letouzey supervised and extended various parts of the
standard library, Stéphane Glondu contributed a few tactics and
improvements, Jean-Marc Notin provided help in debugging, general
maintenance and coqdoc support, Vincent Siles contributed extensions of
the Scheme command and of injection.

Bruno Barras implemented the ``coqchk`` tool: this is a stand-alone
type checker that can be used to certify .vo files. Especially, as this
verifier runs in a separate process, it is granted not to be “hijacked”
by virtually malicious extensions added to |Coq|.

Yves Bertot, Jean-Christophe Filliâtre, Pierre Courtieu and Julien
Forest acted as maintainers of features they implemented in previous
versions of |Coq|.

Julien Narboux contributed to |CoqIDE|. Nicolas Tabareau made the
adaptation of the interface of the old “setoid rewrite” tactic to the
new version. Lionel Mamane worked on the interaction between |Coq| and its
external interfaces. With Samuel Mimram, he also helped making |Coq|
compatible with recent software tools. Russell O’Connor, Cezary
Kaliszyk, Milad Niqui contributed to improve the libraries of integers,
rational, and real numbers. We also thank many users and partners for
suggestions and feedback, in particular Pierre Castéran and Arthur
Charguéraud, the INRIA Marelle team, Georges Gonthier and the
INRIA-Microsoft Mathematical Components team, the Foundations group at
Radboud university in Nijmegen, reporters of bugs and participants to
the Coq-Club mailing list.

| Palaiseau, June 2008
| Hugo Herbelin
|

Details of changes
~~~~~~~~~~~~~~~~~~

Language

- If a fixpoint is not written with an explicit { struct ... }, then
  all arguments are tried successively (from left to right) until one is
  found that satisfies the structural decreasing condition.
- New experimental typeclass system giving ad-hoc polymorphism and
  overloading based on dependent records and implicit arguments.
- New syntax "let 'pat := b in c" for let-binding using irrefutable patterns.
- New syntax "forall {A}, T" for specifying maximally inserted implicit
  arguments in terms.
- Sort of Record/Structure, Inductive and CoInductive defaults to Type
  if omitted.
- (Co)Inductive types can be defined as records
  (e.g. "CoInductive stream := { hd : nat; tl : stream }.")
- New syntax "Theorem id1:t1 ... with idn:tn" for proving mutually dependent
  statements.
- Support for sort-polymorphism on constants denoting inductive types.
- Several evolutions of the module system (handling of module aliases,
  functorial module types, an Include feature, etc).
- Prop now a subtype of Set (predicative and impredicative forms).
- Recursive inductive types in Prop with a single constructor of which
  all arguments are in Prop is now considered to be a singleton
  type. It consequently supports all eliminations to Prop, Set and Type.
  As a consequence, Acc_rect has now a more direct proof [possible source
  of easily fixed incompatibility in case of manual definition of a recursor
  in a recursive singleton inductive type].

Vernacular commands

- Added option Global to "Arguments Scope" for section surviving.
- Added option "Unset Elimination Schemes" to deactivate the automatic
  generation of elimination schemes.
- Modification of the Scheme command so you can ask for the name to be
  automatically computed (e.g. Scheme Induction for nat Sort Set).
- New command "Combined Scheme" to build combined mutual induction
  principles from existing mutual induction principles.
- New command "Scheme Equality" to build a decidable (boolean) equality
  for simple inductive datatypes and a decision property over this equality
  (e.g.  Scheme Equality for nat).
- Added option "Set Equality Scheme" to make automatic the declaration
  of the boolean equality when possible.
- Source of universe inconsistencies now printed when option
  "Set Printing Universes" is activated.
- New option "Set Printing Existential Instances" for making the display of
  existential variable instances explicit.
- Support for option "[id1 ... idn]", and "-[id1 ... idn]", for the
  "compute"/"cbv" reduction strategy, respectively meaning reduce only, or
  everything but, the constants id1 ... idn. "lazy" alone or followed by
  "[id1 ... idn]", and "-[id1 ... idn]" also supported, meaning apply
  all of beta-iota-zeta-delta, possibly restricting delta.
- New command "Strategy" to control the expansion of constants during
  conversion tests. It generalizes commands Opaque and Transparent by
  introducing a range of levels. Lower levels are assigned to constants
  that should be expanded first.
- New options Global and Local to Opaque and Transparent.
- New command "Print Assumptions" to display all variables, parameters
  or axioms a theorem or definition relies on.
- "Add Rec LoadPath" now provides references to libraries using partially
  qualified names (this holds also for coqtop/coqc option -R).
- SearchAbout supports negated search criteria, reference to logical objects
  by their notation, and more generally search of subterms.
- "Declare ML Module" now allows to import .cmxs files when Coq is
  compiled in native code with a version of OCaml that supports native
  Dynlink (>= 3.11).
- Specific sort constraints on Record now taken into account.
- "Print LoadPath" supports a path argument to filter the display.

Libraries

- Several parts of the libraries are now in Type, in particular FSets,
  SetoidList, ListSet, Sorting, Zmisc. This may induce a few
  incompatibilities. In case of trouble while fixing existing development,
  it may help to simply declare Set as an alias for Type (see file
  SetIsType).

- New arithmetical library in theories/Numbers. It contains:

  * an abstract modular development of natural and integer arithmetics
    in Numbers/Natural/Abstract and Numbers/Integer/Abstract
  * an implementation of efficient computational bounded and unbounded
    integers that can be mapped to processor native arithmetics.
    See Numbers/Cyclic/Int31 for 31-bit integers and Numbers/Natural/BigN
    for unbounded natural numbers and Numbers/Integer/BigZ for unbounded
    integers.
  * some proofs that both older libraries Arith, ZArith and NArith and
    newer BigN and BigZ implement the abstract modular development.
    This allows in particular BigN and BigZ to already come with a
    large database of basic lemmas and some generic tactics (ring),

  This library has still an experimental status, as well as the
  processor-acceleration mechanism, but both its abstract and its
  concrete parts are already quite usable and could challenge the use
  of nat, N and Z in actual developments. Moreover, an extension of
  this framework to rational numbers is ongoing, and an efficient
  Q structure is already provided (see Numbers/Rational/BigQ), but
  this part is currently incomplete (no abstract layer and generic
  lemmas).

- Many changes in FSets/FMaps. In practice, compatibility with earlier
  version should be fairly good, but some adaptations may be required.

  * Interfaces of unordered ("weak") and ordered sets have been factorized
    thanks to new features of Coq modules (in particular Include), see
    FSetInterface. Same for maps. Hints in these interfaces have been
    reworked (they are now placed in a "set" database).
  * To allow full subtyping between weak and ordered sets, a field
    "eq_dec" has been added to OrderedType. The old version of OrderedType
    is now called MiniOrderedType and functor MOT_to_OT allow to
    convert to the new version. The interfaces and implementations
    of sets now contain also such a "eq_dec" field.
  * FSetDecide, contributed by Aaron Bohannon, contains a decision
    procedure allowing to solve basic set-related goals (for instance,
    is a point in a particular set ?). See FSetProperties for examples.
  * Functors of properties have been improved, especially the ones about
    maps, that now propose some induction principles. Some properties
    of fold need less hypothesis.
  * More uniformity in implementations of sets and maps: they all use
    implicit arguments, and no longer export unnecessary scopes (see
    bug #1347)
  * Internal parts of the implementations based on AVL have evolved a
    lot. The main files FSetAVL and FMapAVL are now much more
    lightweight now. In particular, minor changes in some functions
    has allowed to fully separate the proofs of operational
    correctness from the proofs of well-balancing: well-balancing is
    critical for efficiency, but not anymore for proving that these
    trees implement our interfaces, hence we have moved these proofs
    into appendix files FSetFullAVL and FMapFullAVL. Moreover, a few
    functions like union and compare have been modified in order to be
    structural yet efficient. The appendix files also contains
    alternative versions of these few functions, much closer to the
    initial Ocaml code and written via the Function framework.

- Library IntMap, subsumed by FSets/FMaps, has been removed from
  Coq Standard Library and moved into a user contribution Cachan/IntMap

- Better computational behavior of some constants (eq_nat_dec and
  le_lt_dec more efficient, Z_lt_le_dec and Positive_as_OT.compare
  transparent, ...) (exceptional source of incompatibilities).

- Boolean operators moved from module Bool to module Datatypes (may need
  to rename qualified references in script and force notations || and &&
  to be at levels 50 and 40 respectively).

- The constructors xI and xO of type positive now have postfix notations
  "~1" and "~0", allowing to write numbers in binary form easily, for instance
  6 is 1~1~0 and 4*p is p~0~0 (see BinPos.v).

- Improvements to NArith (Nminus, Nmin, Nmax), and to QArith (in particular
  a better power function).

- Changes in ZArith: several additional lemmas (used in theories/Numbers),
  especially in Zdiv, Znumtheory, Zpower. Moreover, many results in
  Zdiv have been generalized: the divisor may simply be non-null
  instead of strictly positive (see lemmas with name ending by
  "_full"). An alternative file ZOdiv proposes a different behavior
  (the one of Ocaml) when dividing by negative numbers.

- Changes in Arith: EqNat and Wf_nat now exported from Arith, some
  constructions on nat that were outside Arith are now in (e.g. iter_nat).

- In SetoidList, eqlistA now expresses that two lists have similar elements
  at the same position, while the predicate previously called eqlistA
  is now equivlistA (this one only states that the lists contain the same
  elements, nothing more).

- Changes in Reals:

  * Most statement in "sigT" (including the
    completeness axiom) are now in "sig" (in case of incompatibility,
    use proj1_sig instead of projT1, sig instead of sigT, etc).
  * More uniform naming scheme (identifiers in French moved to English,
    consistent use of 0 -- zero -- instead of O -- letter O --, etc).
  * Lemma on prod_f_SO is now on prod_f_R0.
  * Useless hypothesis of ln_exists1 dropped.
  * New Rlogic.v states a few logical properties about R axioms.
  * RIneq.v extended and made cleaner.

- Slight restructuration of the Logic library regarding choice and classical
  logic. Addition of files providing intuitionistic axiomatizations of
  descriptions: Epsilon.v, Description.v and IndefiniteDescription.v.

- Definition of pred and minus made compatible with the structural
  decreasing criterion for use in fixpoints.

- Files Relations/Rstar.v and Relations/Newman.v moved out to the user
  contribution repository (contribution CoC_History). New lemmas about
  transitive closure added and some bound variables renamed (exceptional
  risk of incompatibilities).

- Syntax for binders in terms (e.g. for "exists") supports anonymous names.

Notations, coercions, implicit arguments and type inference

- More automation in the inference of the return clause of dependent
  pattern-matching problems.
- Experimental allowance for omission of the clauses easily detectable as
  impossible in pattern-matching problems.
- Improved inference of implicit arguments.
- New options "Set Maximal Implicit Insertion", "Set Reversible Pattern
  Implicit", "Set Strongly Strict Implicit" and "Set Printing Implicit
  Defensive" for controlling inference and use of implicit arguments.
- New modifier in "Implicit Arguments" to force an implicit argument to
  be maximally inserted.
- New modifier of "Implicit Arguments" to enrich the set of implicit arguments.
- New options Global and Local to "Implicit Arguments" for section
  surviving or non export outside module.
- Level "constr" moved from 9 to 8.
- Structure/Record now printed as Record (unless option Printing All is set).
- Support for parametric notations defining constants.
- Insertion of coercions below product types refrains to unfold
  constants (possible source of incompatibility).
- New support for fix/cofix in notations.

Tactic Language

- Second-order pattern-matching now working in Ltac "match" clauses
  (syntax for second-order unification variable is "@?X").
- Support for matching on let bindings in match context using syntax
  "H := body" or "H := body : type".
- Ltac accepts integer arguments (syntax is "ltac:nnn" for nnn an integer).
- The general sequence tactical "expr_0 ; [ expr_1 | ... | expr_n ]"
  is extended so that at most one expr_i may have the form "expr .."
  or just "..". Also, n can be different from the number of subgoals
  generated by expr_0. In this case, the value of expr (or idtac in
  case of just "..") is applied to the intermediate subgoals to make
  the number of tactics equal to the number of subgoals.
- A name used as the name of the parameter of a lemma (like f in
  "apply f_equal with (f:=t)") is now interpreted as a ltac variable
  if such a variable exists (this is a possible source of
  incompatibility and it can be fixed by renaming the variables of a
  ltac function into names that do not clash with the lemmas
  parameter names used in the tactic).
- New syntax "Ltac tac ::= ..." to rebind a tactic to a new expression.
- "let rec ... in ... " now supported for expressions without explicit
  parameters; interpretation is lazy to the contrary of "let ... in ...";
  hence, the "rec" keyword can be used to turn the argument of a
  "let ... in ..." into a lazy one.
- Patterns for hypotheses types in "match goal" are now interpreted in
  type_scope.
- A bound variable whose name is not used elsewhere now serves as
  metavariable in "match" and it gets instantiated by an identifier
  (allow e.g. to extract the name of a statement like "exists x, P x").
- New printing of Ltac call trace for better debugging.

Tactics

- New tactics "apply -> term", "apply <- term", "apply -> term in
  ident", "apply <- term in ident" for applying equivalences (iff).

- Slight improvement of the hnf and simpl tactics when applied on
  expressions with explicit occurrences of match or fix.

- New tactics "eapply in", "erewrite", "erewrite in".

- New tactics "ediscriminate", "einjection", "esimplify_eq".

- Tactics "discriminate", "injection", "simplify_eq" now support any
  term as argument. Clause "with" is also supported.

- Unfoldable references can be given by notation's string rather than by name
  in unfold.

- The "with" arguments are now typed using informations from the current goal:
  allows support for coercions and more inference of implicit arguments.

- Application of "f_equal"-style lemmas works better.

- Tactics elim, case, destruct and induction now support variants eelim,
  ecase, edestruct and einduction.

- Tactics destruct and induction now support the "with" option and the
  "in" clause option. If the option "in" is used, an equality is added
  to remember the term to which the induction or case analysis applied
  (possible source of parsing incompatibilities when destruct or induction is
  part of a let-in expression in Ltac; extra parentheses are then required).

- New support for "as" clause in tactics "apply in" and "eapply in".

- Some new intro patterns:

  * intro pattern "?A" genererates a fresh name based on A.
    Caveat about a slight loss of compatibility:
    Some intro patterns don't need space between them. In particular
    intros ?a?b used to be legal and equivalent to intros ? a ? b. Now it
    is still legal but equivalent to intros ?a ?b.
  * intro pattern "(A & ... & Y & Z)" synonym to "(A,....,(Y,Z)))))"
    for right-associative constructs like /\ or exists.

- Several syntax extensions concerning "rewrite":

  * "rewrite A,B,C" can be used to rewrite A, then B, then C. These rewrites
    occur only on the first subgoal: in particular, side-conditions of the
    "rewrite A" are not concerned by the "rewrite B,C".
  * "rewrite A by tac" allows to apply tac on all side-conditions generated by
    the "rewrite A".
  * "rewrite A at n" allows to select occurrences to rewrite: rewrite only
    happen at the n-th exact occurrence of the first successful matching of
    A in the goal.
  * "rewrite 3 A" or "rewrite 3!A" is equivalent to "rewrite A,A,A".
  * "rewrite !A" means rewriting A as long as possible (and at least once).
  * "rewrite 3?A" means rewriting A at most three times.
  * "rewrite ?A" means rewriting A as long as possible (possibly never).
  * many of the above extensions can be combined with each other.

- Introduction patterns better respect the structure of context in presence of
  missing or extra names in nested disjunction-conjunction patterns [possible
  source of rare incompatibilities].

- New syntax "rename a into b, c into d" for "rename a into b; rename c into d"

- New tactics "dependent induction/destruction H [ generalizing id_1 .. id_n ]"
  to do induction-inversion on instantiated inductive families à la BasicElim.

- Tactics "apply" and "apply in" now able to reason modulo unfolding of
  constants (possible source of incompatibility in situations where apply
  may fail, e.g. as argument of a try or a repeat and in a ltac function);
  versions that do not unfold are renamed into "simple apply" and
  "simple apply in" (usable for compatibility or for automation).

- Tactics "apply" and "apply in" now able to traverse conjunctions and to
  select the first matching lemma among the components of the conjunction;
  tactic "apply" also able to apply lemmas of conclusion an empty type.

- Tactic "apply" now supports application of several lemmas in a row.

- Tactics "set" and "pose" can set functions using notation "(f x1..xn := c)".

- New tactic "instantiate" (without argument).

- Tactic firstorder "with" and "using" options have their meaning swapped for
  consistency with auto/eauto (source of incompatibility).

- Tactic "generalize" now supports "at" options to specify occurrences
  and "as" options to name the quantified hypotheses.

- New tactic "specialize H with a" or "specialize (H a)" allows to transform
  in-place a universally-quantified hypothesis (H : forall x, T x) into its
  instantiated form (H : T a). Nota: "specialize" was in fact there in earlier
  versions of Coq, but was undocumented, and had a slightly different behavior.

- New tactic "contradict H" can be used to solve any kind of goal as long as
  the user can provide afterwards a proof of the negation of the hypothesis H.
  If H is already a negation, say ~T, then a proof of T is asked.
  If the current goal is a negation, say ~U, then U is saved in H afterwards,
  hence this new tactic "contradict" extends earlier tactic "swap", which is
  now obsolete.

- Tactics f_equal is now done in ML instead of Ltac: it now works on any
  equality of functions, regardless of the arity of the function.

- New options "before id", "at top", "at bottom" for tactics "move"/"intro".

- Some more debug of reflexive omega (``romega``), and internal clarifications.
  Moreover, romega now has a variant ``romega with *`` that can be also used
  on non-Z goals (nat, N, positive) via a call to a translation tactic named
  zify (its purpose is to Z-ify your goal...). This zify may also be used
  independently of romega.

- Tactic "remember" now supports an "in" clause to remember only selected
  occurrences of a term.

- Tactic "pose proof" supports name overwriting in case of specialization of an
  hypothesis.

- Semi-decision tactic "jp" for first-order intuitionistic logic moved to user
  contributions (subsumed by "firstorder").

Program

- Moved useful tactics in theories/Program and documented them.
- Add Program.Basics which contains standard definitions for functional
  programming (id, apply, flip...)
- More robust obligation handling, dependent pattern-matching and
  well-founded definitions.
- New syntax " dest term as pat in term " for destructing objects using
  an irrefutable pattern while keeping equalities (use this instead of
  "let" in Programs).
- Program CoFixpoint is accepted, Program Fixpoint uses the new way to infer
  which argument decreases structurally.
- Program Lemma, Axiom etc... now permit to have obligations in the statement
  iff they can be automatically solved by the default tactic.
- Renamed "Obligations Tactic" command to "Obligation Tactic".
- New command "Preterm [ of id ]" to see the actual term fed to Coq for
  debugging purposes.
- New option "Transparent Obligations" to control the declaration of
  obligations as transparent or opaque. All obligations are now transparent
  by default, otherwise the system declares them opaque if possible.
- Changed the notations "left" and "right" to "in_left" and "in_right" to hide
  the proofs in standard disjunctions, to avoid breaking existing scripts when
  importing Program. Also, put them in program_scope.

Type Classes

- New "Class", "Instance" and "Program Instance" commands to define
  classes and instances documented in the reference manual.
- New binding construct " [ Class_1 param_1 .. param_n, Class_2 ... ] "
  for binding type classes, usable everywhere.
- New command " Print Classes " and " Print Instances some_class " to
  print tables for typeclasses.
- New default eauto hint database "typeclass_instances" used by the default
  typeclass instance search tactic.
- New theories directory "theories/Classes" for standard typeclasses
  declarations. Module Classes.RelationClasses is a typeclass port of
  Relation_Definitions plus a generic development of algebra on
  n-ary heterogeneous predicates.

Setoid rewriting

- Complete (and still experimental) rewrite of the tactic
  based on typeclasses. The old interface and semantics are
  almost entirely respected, except:

  + Import Setoid is now mandatory to be able to call setoid_replace
    and declare morphisms.

  + "-->", "++>" and "==>" are now right associative notations
    declared at level 55 in scope signature_scope.
    Their introduction may break existing scripts that defined
    them as notations with different levels.

  + One needs to use [Typeclasses unfold [cst]] if [cst] is used
    as an abbreviation hiding products in types of morphisms,
    e.g. if ones redefines [relation] and declares morphisms
    whose type mentions [relation].

  + The [setoid_rewrite]'s semantics change when rewriting with
    a lemma: it can rewrite two different instantiations of the lemma
    at once. Use [setoid_rewrite H at 1] for (almost) the usual semantics.
    [setoid_rewrite] will also try to rewrite under binders now, and can
    succeed on different terms than before. In particular, it will unify under
    let-bound variables. When called through [rewrite], the semantics are
    unchanged though.

  + [Add Morphism term : id] has different semantics when used with
    parametric morphism: it will try to find a relation on the parameters
    too. The behavior has also changed with respect to default relations:
    the most recently declared Setoid/Relation will be used, the documentation
    explains how to customize this behavior.

  + Parametric Relation and Morphism are declared differently, using the
    new [Add Parametric] commands, documented in the manual.

  + Setoid_Theory is now an alias to Equivalence, scripts building objects
    of type Setoid_Theory need to unfold (or "red") the definitions
    of Reflexive, Symmetric and Transitive in order to get the same goals
    as before. Scripts which introduced variables explicitly will not break.

  + The order of subgoals when doing [setoid_rewrite] with side-conditions
    is always the same: first the new goal, then the conditions.

- New standard library modules ``Classes.Morphisms`` declares
  standard morphisms on ``refl`` / ``sym`` / ``trans`` relations.
  ``Classes.Morphisms_Prop`` declares morphisms on propositional
  connectives and ``Classes.Morphisms_Relations`` on generalized predicate
  connectives. ``Classes.Equivalence`` declares notations and tactics
  related to equivalences and ``Classes.SetoidTactics`` defines the
  setoid_replace tactics and some support for the ``Add *`` interface,
  notably the tactic applied automatically before each ``Add Morphism``
  proof.

- User-defined subrelations are supported, as well as higher-order morphisms
  and rewriting under binders. The tactic is also extensible entirely in Ltac.
  The documentation has been updated to cover these features.

- [setoid_rewrite] and [rewrite] now support the [at] modifier to select
  occurrences to rewrite, and both use the [setoid_rewrite] code, even when
  rewriting with leibniz equality if occurrences are specified.

Extraction

- Improved behavior of the Caml extraction of modules: name clashes should
  not happen anymore.

- The command Extract Inductive has now a syntax for infix notations. This
  allows in particular to map Coq lists and pairs onto Caml ones:

  + Extract Inductive list => list [ "[]" "(::)" ].
  + Extract Inductive prod => "(*)" [ "(,)" ].

- In pattern matchings, a default pattern "| _ -> ..." is now used whenever
  possible if several branches are identical. For instance, functions
  corresponding to decidability of equalities are now linear instead of
  quadratic.

- A new instruction Extraction Blacklist id1 .. idn allows to prevent filename
  conflits with existing code, for instance when extracting module List
  to Ocaml.

CoqIDE

- CoqIDE font defaults to monospace so as indentation to be meaningful.
- CoqIDE supports nested goals and any other kind of declaration in the middle
  of a proof.
- Undoing non-tactic commands in CoqIDE works faster.
- New CoqIDE menu for activating display of various implicit informations.
- Added the possibility to choose the location of tabs in coqide:
  (in Edit->Preferences->Misc)
- New Open and Save As dialogs in CoqIDE which filter ``*.v`` files.

Tools

- New stand-alone .vo files verifier "coqchk".
- Extended -I coqtop/coqc option to specify a logical dir: "-I dir -as coqdir".
- New coqtop/coqc option -exclude-dir to exclude subdirs for option -R.
- The binary "parser" has been renamed to "coq-parser".
- Improved coqdoc and dump of globalization information to give more
  meta-information on identifiers. All categories of Coq definitions are
  supported, which makes typesetting trivial in the generated documentation.
  Support for hyperlinking and indexing developments in the tex output
  has been implemented as well.

Miscellaneous

- Coq installation provides enough files so that Ocaml's extensions need not
  the Coq sources to be compiled (this assumes O'Caml 3.10 and Camlp5).
- New commands "Set Whelp Server" and "Set Whelp Getter" to customize the
  Whelp search tool.
- Syntax of "Test Printing Let ref" and "Test Printing If ref" changed into
  "Test Printing Let for ref" and "Test Printing If for ref".
- An overhauled build system (new Makefiles); see dev/doc/build-system.txt.
- Add -browser option to configure script.
- Build a shared library for the C part of Coq, and use it by default on
  non-(Windows or MacOS) systems. Bytecode executables are now pure. The
  behaviour is configurable with -coqrunbyteflags, -coqtoolsbyteflags and
  -custom configure options.
- Complexity tests can be skipped by setting the environment variable
  COQTEST_SKIPCOMPLEXITY.

Version 8.1
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

Coq version 8.1 adds various new functionalities.

Benjamin Grégoire implemented an alternative algorithm to check the
convertibility of terms in the |Coq| type checker. This alternative
algorithm works by compilation to an efficient bytecode that is
interpreted in an abstract machine similar to Xavier Leroy’s ZINC
machine. Convertibility is performed by comparing the normal forms. This
alternative algorithm is specifically interesting for proofs by
reflection. More generally, it is convenient in case of intensive
computations.

Christine Paulin implemented an extension of inductive types allowing
recursively non uniform parameters. Hugo Herbelin implemented
sort-polymorphism for inductive types (now called template polymorphism).

Claudio Sacerdoti Coen improved the tactics for rewriting on arbitrary
compatible equivalence relations. He also generalized rewriting to
arbitrary transition systems.

Claudio Sacerdoti Coen added new features to the module system.

Benjamin Grégoire, Assia Mahboubi and Bruno Barras developed a new, more
efficient and more general simplification algorithm for rings and
semirings.

Laurent Théry and Bruno Barras developed a new, significantly more
efficient simplification algorithm for fields.

Hugo Herbelin, Pierre Letouzey, Julien Forest, Julien Narboux and
Claudio Sacerdoti Coen added new tactic features.

Hugo Herbelin implemented matching on disjunctive patterns.

New mechanisms made easier the communication between |Coq| and external
provers. Nicolas Ayache and Jean-Christophe Filliâtre implemented
connections with the provers cvcl, Simplify and zenon. Hugo Herbelin
implemented an experimental protocol for calling external tools from the
tactic language.

Matthieu Sozeau developed Russell, an experimental language to specify
the behavior of programs with subtypes.

A mechanism to automatically use some specific tactic to solve
unresolved implicit has been implemented by Hugo Herbelin.

Laurent Théry’s contribution on strings and Pierre Letouzey and
Jean-Christophe Filliâtre’s contribution on finite maps have been
integrated to the |Coq| standard library. Pierre Letouzey developed a
library about finite sets “à la Objective Caml”. With Jean-Marc Notin,
he extended the library on lists. Pierre Letouzey’s contribution on
rational numbers has been integrated and extended.

Pierre Corbineau extended his tactic for solving first-order statements.
He wrote a reflection-based intuitionistic tautology solver.

Pierre Courtieu, Julien Forest and Yves Bertot added extra support to
reason on the inductive structure of recursively defined functions.

Jean-Marc Notin significantly contributed to the general maintenance of
the system. He also took care of ``coqdoc``.

Pierre Castéran contributed to the documentation of (co-)inductive types
and suggested improvements to the libraries.

Pierre Corbineau implemented a declarative mathematical proof language,
usable in combination with the tactic-based style of proof.

Finally, many users suggested improvements of the system through the
Coq-Club mailing list and bug-tracker systems, especially user groups
from INRIA Rocquencourt, Radboud University, University of Pennsylvania
and Yale University.

| Palaiseau, July 2006
| Hugo Herbelin
|

Details of changes in 8.1beta
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Logic

- Added sort-polymorphism on inductive families
- Allowance for recursively non uniform parameters in inductive types

Syntax

- No more support for version 7 syntax and for translation to version 8 syntax.
- In fixpoints, the { struct ... } annotation is not mandatory any more when
  only one of the arguments has an inductive type
- Added disjunctive patterns in match-with patterns
- Support for primitive interpretation of string literals
- Extended support for Unicode ranges

Vernacular commands

- Added "Print Ltac qualid" to print a user defined tactic.
- Added "Print Rewrite HintDb" to print the content of a DB used by
  autorewrite.
- Added "Print Canonical Projections".
- Added "Example" as synonym of "Definition".
- Added "Proposition" and "Corollary" as extra synonyms of "Lemma".
- New command "Whelp" to send requests to the Helm database of proofs
  formalized in the Calculus of Inductive Constructions.
- Command "functional induction" has been re-implemented from the new
  "Function" command.

Ltac and tactic syntactic extensions

- New primitive "external" for communication with tool external to Coq
- New semantics for "match t with": if a clause returns a
  tactic, it is now applied to the current goal. If it fails, the next
  clause or next matching subterm is tried (i.e. it behaves as "match
  goal with" does). The keyword "lazymatch" can be used to delay the
  evaluation of tactics occurring in matching clauses.
- Hint base names can be parametric in auto and trivial.
- Occurrence values can be parametric in unfold, pattern, etc.
- Added entry constr_may_eval for tactic extensions.
- Low-priority term printer made available in ML-written tactic extensions.
- "Tactic Notation" extended to allow notations of tacticals.

Tactics

- New implementation and generalization of ``setoid_*`` (``setoid_rewrite``,
  ``setoid_symmetry``, ``setoid_transitivity``, ``setoid_reflexivity`` and ``autorewite``).
  New syntax for declaring relations and morphisms (old syntax still working
  with minor modifications, but deprecated).

- New implementation (still experimental) of the ring tactic with a built-in
  notion of coefficients and a better usage of setoids.

- New conversion tactic "vm_compute": evaluates the goal (or an hypothesis)
  with a call-by-value strategy, using the compiled version of terms.

- When rewriting H where H is not directly a Coq equality, search first H for
  a registered setoid equality before starting to reduce in H. This is unlikely
  to break any script. Should this happen nonetheless, one can insert manually
  some "unfold ... in H" before rewriting.

- Fixed various bugs about (setoid) rewrite ... in ... (in particular bug #5941)

- "rewrite ... in" now accepts a clause as place where to rewrite instead of
  just a simple hypothesis name. For instance:
  ``rewrite H in H1,H2 |- *`` means ``rewrite H in H1; rewrite H in H2; rewrite H``
  ``rewrite H in * |-``  will do try ``rewrite H in Hi`` for all hypothesis Hi <> H.

- Added "dependent rewrite term" and "dependent rewrite term in hyp".

- Added "autorewrite with ... in hyp [using ...]".

- Tactic "replace" now accepts a "by" tactic clause.

- Added "clear - id" to clear all hypotheses except the ones depending in id.

- The argument of Declare Left Step and Declare Right Step is now a term
  (it used to be a reference).

- Omega now handles arbitrary precision integers.

- Several bug fixes in Reflexive Omega (romega).

- Idtac can now be left implicit in a [...|...] construct: for instance,
  [ foo | | bar ] stands for [ foo | idtac | bar ].

- Fixed a "fold" bug (non critical but possible source of incompatibilities).

- Added classical_left and classical_right which transforms ``|- A \/ B`` into
  ``~B |- A`` and ``~A |- B`` respectively.

- Added command "Declare Implicit Tactic" to set up a default tactic to be
  used to solve unresolved subterms of term arguments of tactics.

- Better support for coercions to Sortclass in tactics expecting type
  arguments.

- Tactic "assert" now accepts "as" intro patterns and "by" tactic clauses.

- New tactic "pose proof" that generalizes "assert (id:=p)" with intro patterns.

- New introduction pattern "?" for letting Coq choose a name.

- Introduction patterns now support side hypotheses (e.g. intros [|] on
  "(nat -> nat) -> nat" works).

- New introduction patterns "->" and "<-" for immediate rewriting of
  introduced hypotheses.

- Introduction patterns coming after non trivial introduction patterns now
  force full introduction of the first pattern (e.g. ``intros [[|] p]`` on
  ``nat->nat->nat`` now behaves like ``intros [[|?] p]``)

- Added "eassumption".

- Added option 'using lemmas' to auto, trivial and eauto.

- Tactic "congruence" is now complete for its intended scope (ground
  equalities and inequalities with constructors). Furthermore, it
  tries to equates goal and hypotheses.

- New tactic "rtauto" solves pure propositional logic and gives a
  reflective version of the available proof.

- Numbering of "pattern", "unfold", "simpl", ... occurrences in "match
  with" made consistent with the printing of the return clause after
  the term to match in the "match-with" construct (use "Set Printing All"
  to see hidden occurrences).

- Generalization of induction "induction x1...xn using scheme" where
  scheme is an induction principle with complex predicates (like the
  ones generated by function induction).

- Some small Ltac tactics has been added to the standard library
  (file Tactics.v):

  * f_equal : instead of using the different f_equalX lemmas
  * case_eq : a "case" without loss of information. An equality
    stating the current situation is generated in every sub-cases.
  * swap : for a negated goal ~B and a negated hypothesis H:~A,
    swap H asks you to prove A from hypothesis B
  * revert : revert H is generalize H; clear H.

Extraction

- All type parts should now disappear instead of sometimes producing _
  (for instance in Map.empty).
- Haskell extraction: types of functions are now printed, better
  unsafeCoerce mechanism, both for hugs and ghc.
- Scheme extraction improved, see http://www.pps.jussieu.fr/~letouzey/scheme.
- Many bug fixes.

Modules

- Added "Locate Module qualid" to get the full path of a module.
- Module/Declare Module syntax made more uniform.
- Added syntactic sugar "Declare Module Export/Import" and
  "Module Export/Import".
- Added syntactic sugar "Module M(Export/Import X Y: T)" and
  "Module Type M(Export/Import X Y: T)"
  (only for interactive definitions)
- Construct "with" generalized to module paths:
  T with (Definition|Module) M1.M2....Mn.l := l'.

Notations

- Option "format" aware of recursive notations.
- Added insertion of spaces by default in recursive notations w/o separators.
- No more automatic printing box in case of user-provided printing "format".
- New notation "exists! x:A, P" for unique existence.
- Notations for specific numerals now compatible with generic notations of
  numerals (e.g. "1" can be used to denote the unit of a group without
  hiding 1%nat)

Libraries

- New library on String and Ascii characters (contributed by L. Thery).
- New library FSets+FMaps of finite sets and maps.
- New library QArith on rational numbers.
- Small extension of Zmin.V, new Zmax.v, new Zminmax.v.
- Reworking and extension of the files on classical logic and
  description principles (possible incompatibilities)
- Few other improvements in ZArith potentially exceptionally breaking the
  compatibility (useless hypothesys of Zgt_square_simpl and
  Zlt_square_simpl removed; fixed names mentioning letter O instead of
  digit 0; weaken premises in Z_lt_induction).
- Restructuration of Eqdep_dec.v and Eqdep.v: more lemmas in Type.
- Znumtheory now contains a gcd function that can compute within Coq.
- More lemmas stated on Type in Wf.v, removal of redundant Acc_iter and
  Acc_iter2.
- Change of the internal names of lemmas in OmegaLemmas.
- Acc in Wf.v and clos_refl_trans in Relation_Operators.v now rely on
  the allowance for recursively non uniform parameters (possible
  source of incompatibilities: explicit pattern-matching on these
  types may require to remove the occurrence associated to their
  recursively non uniform parameter).
- Coq.List.In_dec has been set transparent (this may exceptionally break
  proof scripts, set it locally opaque for compatibility).
- More on permutations of lists in List.v and Permutation.v.
- List.v has been much expanded.
- New file SetoidList.v now contains results about lists seen with
  respect to a setoid equality.
- Library NArith has been expanded, mostly with results coming from
  Intmap (for instance a bitwise xor), plus also a bridge between N and
  Bitvector.
- Intmap has been reorganized. In particular its address type "addr" is
  now N. User contributions known to use Intmap have been adapted
  accordingly. If you're using this library please contact us.
  A wrapper FMapIntMap now presents Intmap as a particular implementation
  of FMaps. New developments are strongly encouraged to use either this
  wrapper or any other implementations of FMap instead of using directly
  this obsolete Intmap.

Tools

- New semantics for coqtop options ("-batch" expects option "-top dir"
  for loading vernac file that contains definitions).
- Tool coq_makefile now removes custom targets that are file names in
  "make clean"
- New environment variable COQREMOTEBROWSER to set the command invoked
  to start the remote browser both in Coq and coqide. Standard syntax:
  "%s" is the placeholder for the URL.

Details of changes in 8.1gamma
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Syntax

- changed parsing precedence of let/in and fun constructions of Ltac:
  let x := t in e1; e2 is now parsed as let x := t in (e1;e2).

Language and commands

- Added sort-polymorphism for definitions in Type (but finally abandoned).
- Support for implicit arguments in the types of parameters in
  (co-)fixpoints and (co-)inductive declarations.
- Improved type inference: use as much of possible general information.
  before applying irreversible unification heuristics (allow e.g. to
  infer the predicate in "(exist _ 0 (refl_equal 0) : {n:nat | n=0 })").
- Support for Miller-Pfenning's patterns unification in type synthesis
  (e.g. can infer P such that P x y = phi(x,y)).
- Support for "where" clause in cofixpoint definitions.
- New option "Set Printing Universes" for making Type levels explicit.

Tactics

- Improved implementation of the ring and field tactics. For compatibility
  reasons, the previous tactics are renamed as legacy ring and legacy field,
  but should be considered as deprecated.
- New declarative mathematical proof language.
- Support for argument lists of arbitrary length in Tactic Notation.
- ``rewrite ... in H`` now fails if ``H`` is used either in an hypothesis
  or in the goal.
- The semantics of ``rewrite ... in *`` has been slightly modified (see doc).
- Support for ``as`` clause in tactic injection.
- New forward-reasoning tactic "apply in".
- Ltac fresh operator now builds names from a concatenation of its arguments.
- New ltac tactic "remember" to abstract over a subterm and keep an equality
- Support for Miller-Pfenning's patterns unification in apply/rewrite/...
  (may lead to few incompatibilities - generally now useless tactic calls).

Bug fixes

- Fix for notations involving basic "match" expressions.
- Numerous other bugs solved (a few fixes may lead to incompatibilities).

Details of changes in 8.1
~~~~~~~~~~~~~~~~~~~~~~~~~

Bug fixes

- Many bugs have been fixed (cf coq-bugs web page)

Tactics

- New tactics ring, ring_simplify and new tactic field now able to manage
  power to a positive integer constant. Tactic ring on Z and R, and
  field on R manage power (may lead to incompatibilities with V8.1gamma).
- Tactic field_simplify now applicable in hypotheses.
- New field_simplify_eq for simplifying field equations into ring equations.
- Tactics ring, ring_simplify, field, field_simplify and field_simplify_eq
  all able to apply user-given equations to rewrite monoms on the fly
  (see documentation).

Libraries

- New file ConstructiveEpsilon.v defining an epsilon operator and
  proving the axiom of choice constructively for a countable domain
  and a decidable predicate.

Version 8.0
-----------

Summary of changes
~~~~~~~~~~~~~~~~~~

Coq version 8 is a major revision of the |Coq| proof assistant. First, the
underlying logic is slightly different. The so-called *impredicativity*
of the sort Set has been dropped. The main reason is that it is
inconsistent with the principle of description which is quite a useful
principle for formalizing mathematics within classical logic. Moreover,
even in an constructive setting, the impredicativity of Set does not add
so much in practice and is even subject of criticism from a large part
of the intuitionistic mathematician community. Nevertheless, the
impredicativity of Set remains optional for users interested in
investigating mathematical developments which rely on it.

Secondly, the concrete syntax of terms has been completely revised. The
main motivations were

-  a more uniform, purified style: all constructions are now lowercase,
   with a functional programming perfume (e.g. abstraction is now
   written fun), and more directly accessible to the novice (e.g.
   dependent product is now written forall and allows omission of
   types). Also, parentheses are no longer mandatory for function
   application.

-  extensibility: some standard notations (e.g. “<” and “>”) were
   incompatible with the previous syntax. Now all standard arithmetic
   notations (=, +, \*, /, <, <=, ... and more) are directly part of the
   syntax.

Together with the revision of the concrete syntax, a new mechanism of
*interpretation scopes* permits to reuse the same symbols (typically +,
-, \*, /, <, <=) in various mathematical theories without any
ambiguities for |Coq|, leading to a largely improved readability of |Coq|
scripts. New commands to easily add new symbols are also provided.

Coming with the new syntax of terms, a slight reform of the tactic
language and of the language of commands has been carried out. The
purpose here is a better uniformity making the tactics and commands
easier to use and to remember.

Thirdly, a restructuring and uniformization of the standard library of
Coq has been performed. There is now just one Leibniz equality usable
for all the different kinds of |Coq| objects. Also, the set of real
numbers now lies at the same level as the sets of natural and integer
numbers. Finally, the names of the standard properties of numbers now
follow a standard pattern and the symbolic notations for the standard
definitions as well.

The fourth point is the release of |CoqIDE|, a new graphical gtk2-based
interface fully integrated with |Coq|. Close in style to the Proof General
Emacs interface, it is faster and its integration with |Coq| makes
interactive developments more friendly. All mathematical Unicode symbols
are usable within |CoqIDE|.

Finally, the module system of |Coq| completes the picture of |Coq| version
8.0. Though released with an experimental status in the previous version
7.4, it should be considered as a salient feature of the new version.

Besides, |Coq| comes with its load of novelties and improvements: new or
improved tactics (including a new tactic for solving first-order
statements), new management commands, extended libraries.

Bruno Barras and Hugo Herbelin have been the main contributors of the
reflection and the implementation of the new syntax. The smart automatic
translator from old to new syntax released with |Coq| is also their work
with contributions by Olivier Desmettre.

Hugo Herbelin is the main designer and implementer of the notion of
interpretation scopes and of the commands for easily adding new
notations.

Hugo Herbelin is the main implementer of the restructured standard library.

Pierre Corbineau is the main designer and implementer of the new tactic
for solving first-order statements in presence of inductive types. He is
also the maintainer of the non-domain specific automation tactics.

Benjamin Monate is the developer of the |CoqIDE| graphical interface with
contributions by Jean-Christophe Filliâtre, Pierre Letouzey, Claude
Marché and Bruno Barras.

Claude Marché coordinated the edition of the Reference Manual for |Coq|
V8.0.

Pierre Letouzey and Jacek Chrząszcz respectively maintained the
extraction tool and module system of |Coq|.

Jean-Christophe Filliâtre, Pierre Letouzey, Hugo Herbelin and other
contributors from Sophia-Antipolis and Nijmegen participated in
extending the library.

Julien Narboux built a NSIS-based automatic |Coq| installation tool for
the Windows platform.

Hugo Herbelin and Christine Paulin coordinated the development which was
under the responsibility of Christine Paulin.

| Palaiseau & Orsay, Apr. 2004
| Hugo Herbelin & Christine Paulin
| (updated Apr. 2006)
|

Details of changes in 8.0beta old syntax
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Logic

- Set now predicative by default
- New option -impredicative-set to set Set impredicative
- The standard library doesn't need impredicativity of Set and is
  compatible with the classical axioms which contradict Set impredicativity

Syntax for arithmetic

- Notation "=" and "<>" in Z and R are no longer implicitly in Z or R
  (with possible introduction of a coercion), use <Z>...=... or
  <Z>...<>... instead
- Locate applied to a simple string (e.g. "+") searches for all
  notations containing this string

Vernacular commands

- "Declare ML Module" now allows to import .cma files. This avoids to use a
  bunch of "Declare ML Module" statements when using several ML files.
- "Set Printing Width n" added, allows to change the size of width printing.
- "Implicit Variables Type x,y:t" (new syntax: "Implicit Types x y:t")
  assigns default types for binding variables.
- Declarations of Hints and Notation now accept a "Local" flag not to
  be exported outside the current file even if not in section
- "Print Scopes" prints all notations
- New command "About name" for light printing of type, implicit arguments, etc.
- New command "Admitted" to declare incompletely proven statement as axioms
- New keyword "Conjecture" to declare an axiom intended to be provable
- SearchAbout can now search for lemmas referring to more than one constant
  and on substrings of the name of the lemma
- "Print Implicit" displays the implicit arguments of a constant
- Locate now searches for all names having a given suffix
- New command "Functional Scheme" for building an induction principle
  from a function defined by case analysis and fix.

Commands

- new coqtop/coqc option -dont-load-proofs not to load opaque proofs in memory

Implicit arguments

- Inductive in sections declared with implicits now "discharged" with
  implicits (like constants and variables)
- Implicit Arguments flags are now synchronous with reset
- New switch "Unset/Set Printing Implicits" (new syntax: "Unset/Set Printing
  Implicit") to globally control printing of implicits

Grammar extensions

- Many newly supported UTF-8 encoded unicode blocks
  - Greek letters (0380-03FF), Hebrew letters (U05D0-05EF), letter-like
  symbols (2100-214F, that includes double N,Z,Q,R), prime
  signs (from 2080-2089) and characters from many written languages
  are valid in identifiers
  - mathematical operators (2200-22FF), supplemental mathematical
  operators (2A00-2AFF), miscellaneous technical (2300-23FF that
  includes sqrt symbol), miscellaneous symbols (2600-26FF), arrows
  (2190-21FF and 2900-297F), invisible mathematical operators (from
  2080-2089), ... are valid symbols

Library

- New file about the factorial function in Arith

- An additional elimination Acc_iter for Acc, simpler than Acc_rect.
  This new elimination principle is used for definition well_founded_induction.

- New library NArith on binary natural numbers

- R is now of type Set

- Restructuration in ZArith library

  + "true_sub" used in Zplus now a definition, not a local one (source
    of incompatibilities in proof referring to true_sub, may need extra Unfold)
  + Some lemmas about minus moved from fast_integer to Arith/Minus.v
    (le_minus, lt_mult_left) (theoretical source of incompatibilities)
  + Several lemmas moved from auxiliary.v and zarith_aux.v to
    fast_integer.v (theoretical source of incompatibilities)
  + Variables names of iff_trans changed (source of incompatibilities)
  + ZArith lemmas named ``OMEGA`` something or ``fast_`` something, and lemma ``new_var``
    are now out of ZArith (except ``OMEGA2``)
  + Redundant ZArith lemmas have been renamed: for the following pairs,
    use the second name (Zle_Zmult_right2, Zle_mult_simpl), (OMEGA2,
    Zle_0_plus), (Zplus_assoc_l, Zplus_assoc), (Zmult_one, Zmult_1_n),
    (Zmult_assoc_l, Zmult_assoc), (Zmult_minus_distr, Zmult_Zminus_distr_l)
    (add_un_double_moins_un_xO, is_double_moins_un),
    (Rlt_monotony_rev,Rlt_monotony_contra) (source of incompatibilities)

- Few minor changes (no more implicit arguments in
  Zmult_Zminus_distr_l and Zmult_Zminus_distr_r, lemmas moved from
  Zcomplements to other files) (rare source of incompatibilities)

- New lemmas provided by users added

Tactic language

- Fail tactic now accepts a failure message
- Idtac tactic now accepts a message
- New primitive tactic "FreshId" (new syntax: "fresh") to generate new names
- Debugger prints levels of calls

Tactics

- Replace can now replace proofs also
- Fail levels are now decremented at "Match Context" blocks only and
  if the right-hand-side of "Match term With" are tactics, these
  tactics are never evaluated immediately and do not induce
  backtracking (in contrast with "Match Context")
- Quantified names now avoid global names of the current module (like
  Intro names did) [source of rare incompatibilities: 2 changes in the set of
  user contribs]
- NewDestruct/NewInduction accepts intro patterns as introduction names
- NewDestruct/NewInduction now work for non-inductive type using option "using"
- A NewInduction naming bug for inductive types with functional
  arguments (e.g. the accessibility predicate) has been fixed (source
  of incompatibilities)
- Symmetry now applies to hypotheses too
- Inversion now accept option "as [ ... ]" to name the hypotheses
- Contradiction now looks also for contradictory hypotheses stating ~A and A
  (source of incompatibility)
- "Contradiction c" try to find an hypothesis in context which
  contradicts the type of c
- Ring applies to new library NArith (require file NArithRing)
- Field now works on types in Set
- Auto with reals now try to replace le by ge (Rge_le is no longer an
  immediate hint), resulting in shorter proofs
- Instantiate now works in hyps (syntax : Instantiate in ...)
- Some new tactics : EConstructor, ELeft, Eright, ESplit, EExists
- New tactic "functional induction" to perform case analysis and
  induction following the definition of a function.
- Clear now fails when trying to remove a local definition used by
  a constant appearing in the current goal

Extraction (See details in plugins/extraction/CHANGES)

- The old commands: 	(Recursive) Extraction Module M.
  are now:              (Recursive) Extraction Library M.
  To use these commands, M should come from a library M.v
- The other syntax Extraction & Recursive Extraction now accept
  module names as arguments.

Bugs

- see coq-bugs server for the complete list of fixed bugs

Miscellaneous

- Implicit parameters of inductive types definition now taken into
  account for inferring other implicit arguments

Incompatibilities

- Persistence of true_sub (4 incompatibilities in Coq user contributions)
- Variable names of some constants changed for a better uniformity (2 changes
  in Coq user contributions)
- Naming of quantified names in goal now avoid global names (2 occurrences)
- NewInduction naming for inductive types with functional arguments
  (no incompatibility in Coq user contributions)
- Contradiction now solve more goals (source of 2 incompatibilities)
- Merge of eq and eqT may exceptionally result in subgoals now
  solved automatically
- Redundant pairs of ZArith lemmas may have different names: it may
  cause "Apply/Rewrite with" to fail if using the first name of a pair
  of redundant lemmas (this is solved by renaming the variables bound by
  "with"; 3 incompatibilities in Coq user contribs)
- ML programs referring to constants from fast_integer.v must use
  "Coqlib.gen_constant_modules Coqlib.zarith_base_modules" instead

Details of changes in 8.0beta new syntax
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

New concrete syntax

- A completely new syntax for terms
- A more uniform syntax for tactics and the tactic language
- A few syntactic changes for vernacular commands
- A smart automatic translator translating V8.0 files in old syntax to
  files valid for V8.0

Syntax extensions

- "Grammar" for terms disappears
- "Grammar" for tactics becomes "Tactic Notation"
- "Syntax" disappears
- Introduction of a notion of interpretation scope allowing to use the
  same notations in various contexts without using specific delimiters
  (e.g the same expression "4<=3+x" is interpreted either in "nat",
  "positive", "N" (previously "entier"), "Z", "R", depending on which
  interpretation scope is currently open) [see documentation for details]
- Notation now mandatorily requires a precedence and associativity
  (default was to set precedence to 1 and associativity to none)

Revision of the standard library

- Many lemmas and definitions names have been made more uniform mostly
  in Arith, NArith, ZArith and Reals (e.g : "times" -> "Pmult",
  "times_sym" -> "Pmult_comm", "Zle_Zmult_pos_right" ->
  "Zmult_le_compat_r", "SUPERIEUR" -> "Gt", "ZERO" -> "Z0")
- Order and names of arguments of basic lemmas on nat, Z, positive and R
  have been made uniform.
- Notions of Coq initial state are declared with (strict) implicit arguments
- eq merged with eqT: old eq disappear, new eq (written =) is old eqT
  and new eqT is syntactic sugar for new eq (notation == is an alias
  for = and is written as it, exceptional source of incompatibilities)
- Similarly, ex, ex2, all, identity are merged with exT, exT2, allT, identityT
- Arithmetical notations for nat, positive, N, Z, R, without needing
  any backquote or double-backquotes delimiters.
- In Lists: new concrete notations; argument of nil is now implicit
- All changes in the library are taken in charge by the translator

Semantical changes during translation

- Recursive keyword set by default (and no longer needed) in Tactic Definition
- Set Implicit Arguments is strict by default in new syntax
- reductions in hypotheses of the form "... in H" now apply to the type
  also if H is a local definition
- etc

Gallina

- New syntax of the form "Inductive bool : Set := true, false : bool." for
  enumerated types
- Experimental syntax of the form p.(fst) for record projections
  (activable with option "Set Printing Projections" which is
  recognized by the translator)

Known problems of the automatic translation

- iso-latin-1 characters are no longer supported: move your files to
  7-bits ASCII or unicode before translation (switch to unicode is
  automatically done if a file is loaded and saved again by coqide)
- Renaming in ZArith: incompatibilities in Coq user contribs due to
  merging names INZ, from Reals, and inject_nat.
- Renaming and new lemmas in ZArith: may clash with names used by users
- Restructuration of ZArith: replace requirement of specific modules
  in ZArith by "Require Import ZArith_base" or "Require Import ZArith"
- Some implicit arguments must be made explicit before translation: typically
  for "length nil", the implicit argument of length must be made explicit
- Grammar rules, Infix notations and V7.4 Notations must be updated wrt the
  new scheme for syntactic extensions (see translator documentation)
- Unsafe for annotation Cases when constructors coercions are used or when
  annotations are eta-reduced predicates

Details of changes in 8.0
~~~~~~~~~~~~~~~~~~~~~~~~~

Vernacular commands

- New option "Set Printing All" to deactivate all high-level forms of
  printing (implicit arguments, coercions, destructing let,
  if-then-else, notations, projections)
- "Functional Scheme" and "Functional Induction" extended to polymorphic
  types and dependent types
- Notation now allows recursive patterns, hence recovering parts of the
  functionalities of pre-V8 Grammar/Syntax commands
- Command "Print." discontinued.
- Redundant syntax "Implicit Arguments On/Off" discontinued

New syntax

- Semantics change of the if-then-else construction in new syntax:
  "if c then t1 else t2" now stands for
  "match c with c1 _ ... _ => t1 | c2 _ ... _ => t2 end"
  with no dependency of t1 and t2 in the arguments of the constructors;
  this may cause incompatibilities for files translated using coq 8.0beta

Interpretation scopes

- Delimiting key %bool for bool_scope added
- Import no more needed to activate argument scopes from a module

Tactics and the tactic Language

- Semantics of "assert" is now consistent with the reference manual
- New tactics stepl and stepr for chaining transitivity steps
- Tactic "replace ... with ... in" added
- Intro patterns now supported in Ltac (parsed with prefix "ipattern:")

Executables and tools

- Added option -top to change the name of the toplevel module "Top"
- Coqdoc updated to new syntax and now part of Coq sources
- XML exportation tool now exports the structure of vernacular files
  (cf chapter 13 in the reference manual)

User contributions

- User contributions have been updated to the new syntax

Bug fixes

- Many bugs have been fixed (cf coq-bugs web page)
