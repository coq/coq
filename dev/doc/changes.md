## Changes between Coq 8.8 and Coq 8.9

### ML API

Names

- In `Libnames`, the type `reference` and its two constructors `Qualid` and
  `Ident` have been removed in favor of `qualid`. `Qualid` is now the identity,
  `Ident` can be replaced by `qualid_of_ident`. Matching over `reference` can be
  replaced by a test using `qualid_is_ident`. Extracting the `ident` part of a
  `qualid` can be done using `qualid_basename`.

Misctypes

- Syntax for universe sorts and kinds has been moved from `Misctypes`
  to `Glob_term`, as these are turned into kernel terms by
  `Pretyping`.

Proof engine

- More functions have been changed to use `EConstr`, notably the
  functions in `Evd`, and in particular `Evd.define`.

  Note that the core function `EConstr.to_constr` now _enforces_ by
  default that the resulting term is ground, that is to say, free of
  Evars. This is usually what you want, as open terms should be of
  type `EConstr.t` to benefit from the invariants the `EConstr` API is
  meant to guarantee.

  In case you'd like to violate this API invariant, you can use the
  `abort_on_undefined_evars` flag to `EConstr.to_constr`, but note
  that setting this flag to false is deprecated so it is only meant to
  be used as to help port pre-EConstr code.

- A few type alias have been deprecated, in all cases the message
  should indicate what the canonical form is. An important change is
  the move of `Globnames.global_reference` to `Names.GlobRef.t`.

- Unification API returns `evar_map option` instead of `bool * evar_map`
  with the guarantee that the `evar_map` was unchanged if the boolean
  was false.

ML Libraries used by Coq

- Introduction of a `Smart` module for collecting `smart*` functions, e.g.
  `Array.Smart.map`.
- Uniformization of some names, e.g. `Array.Smart.fold_left_map` instead
  of `Array.smartfoldmap`.

Printer.ml API

- The mechanism in `Printer` that allowed dynamically overriding `pr_subgoals`,
  `pr_subgoal` and `pr_goal` was removed to simplify the code.  It was
  earlier used by PCoq.

Kernel

- The following renamings happened:
  - `Context.Rel.t` into `Constr.rel_context`
  - `Context.Named.t` into `Constr.named_context`
  - `Context.Compacted.t` into `Constr.compacted_context`
  - `Context.Rel.Declaration.t` into `Constr.rel_declaration`
  - `Context.Named.Declaration.t` into `Constr.named_declaration`
  - `Context.Compacted.Declaration.t` into `Constr.compacted_declaration`

Source code organization

- We have eliminated / fused some redundant modules and relocated a
  few interfaces files. The `intf` folder is gone, and now for example
  `Constrexpr` is located in `interp/`, `Vernacexpr` in `vernac/` and
  so on. Changes should be compatible, but in a few cases stricter
  layering requirements may mean that functions have moved. In all
  cases adapting is a matter of changing the module name.

Vernacular commands

- The implementation of vernacular commands has been refactored so it
  is self-contained now, including the parsing and extension
  mechanisms. This involves a couple of non-backward compatible
  changes due to layering issues, where some functions have been moved
  from `Pcoq` to `Pvernac` and from `Vernacexpr` to modules in
  `tactics/`. In all cases adapting is a matter of changing the module
  name.

Primitive number parsers

- For better modularity, the primitive parsers for `positive`, `N` and `Z`
  have been split over three files (`plugins/syntax/positive_syntax.ml`,
  `plugins/syntax/n_syntax.ml`, `plugins/syntax/z_syntax.ml`).

Parsing

- Manual uses of the `Pcoq.Gram` module have been deprecated. Wrapper modules
  `Pcoq.Entry` and `Pcoq.Parsable` were introduced to replace it.

Termops

- Internal printing functions have been placed under the
  `Termops.Internal` namespace.

### Unit testing

The test suite now allows writing unit tests against OCaml code in the Coq
code base. Those unit tests create a dependency on the OUnit test framework.

### Transitioning away from Camlp5

In an effort to reduce dependency on camlp5, the use of several grammar macros
is discouraged. Coq is now shipped with its own preprocessor, called coqpp,
which serves the same purpose as camlp5.

To perform the transition to coqpp macros, one first needs to change the
extension of a macro file from `.ml4` to `.mlg`. Not all camlp5 macros are
handled yet.

Due to parsing constraints, the syntax of the macros is slightly different, but
updating the source code is mostly a matter of straightforward
search-and-replace. The main differences are summarized below.

#### OCaml code

Every piece of toplevel OCaml code needs to be wrapped into braces.

For instance, code of the form
```
let myval = 0
```
should be turned into
```
{
let myval = 0
}
```

#### TACTIC EXTEND

Steps to perform:
- replace the brackets enclosing OCaml code in actions with braces
- if not there yet, add a leading `|` to the first rule

For instance, code of the form:
```
TACTIC EXTEND my_tac
  [ "tac1" int_or_var(i) tactic(t) ] -> [ mytac1 ist i t ]
| [ "tac2" tactic(t) ] -> [ mytac2 t ]
END
```
should be turned into
```
TACTIC EXTEND my_tac
| [ "tac1" int_or_var(i) tactic(t) ] -> { mytac1 ist i t }
| [ "tac2" tactic(t) ] -> { mytac2 t }
END
```

#### VERNAC EXTEND

Not handled yet.

#### ARGUMENT EXTEND

Not handled yet.

#### GEXTEND

Most plugin writers do not need this low-level interface, but for the sake of
completeness we document it.

Steps to perform are:
- replace `GEXTEND` with `GRAMMAR EXTEND`
- wrap every occurrence of OCaml code in actions into braces `{ }`

For instance, code of the form
```
GEXTEND Gram
   GLOBAL: my_entry;

my_entry:
[ [ x = bar; y = qux -> do_something x y
  | "("; z = LIST0 my_entry; ")" -> do_other_thing z
] ];
END
```
should be turned into
```
GRAMMAR EXTEND Gram
   GLOBAL: my_entry;

my_entry:
[ [ x = bar; y = qux -> { do_something x y }
  | "("; z = LIST0 my_entry; ")" -> { do_other_thing z }
] ];
END
```

Caveats:
- No `GLOBAL` entries mean that they are all local, while camlp5 special-cases
  this as a shorthand for all global entries. Solution: always define a `GLOBAL`
  section.
- No complex patterns allowed in token naming. Solution: match on it inside the
  OCaml quotation.

## Changes between Coq 8.7 and Coq 8.8

### Bug tracker

As of 18/10/2017, Coq uses [GitHub issues](https://github.com/coq/coq/issues)
as bug tracker.
Old bug reports were migrated from Bugzilla to GitHub issues using
[this migration script](https://gist.github.com/Zimmi48/d923e52f64fe17c72852d9c148bfcdc6#file-bugzilla2github)
as detailed in [this blog post](https://www.theozimmermann.net/2017/10/bugzilla-to-github/).

All the bugs with a number below 1154 had to be renumbered, you can find
a correspondence table [here](/dev/bugzilla2github_stripped.csv).
All the other bugs kept their number.

### ML API

General deprecation

- All functions marked `[@@ocaml.deprecated]` in 8.7 have been
  removed. Please, make sure your plugin is warning-free in 8.7 before
  trying to port it over 8.8.

Proof engine

  Due to the introduction of `EConstr` in 8.7, it is not necessary to
  track "goal evar normal form status" anymore, thus the type `'a
  Proofview.Goal.t` loses its ghost argument. This may introduce some
  minor incompatibilities at the typing level. Code-wise, things
  should remain the same.

We removed the following functions:

- `Universes.unsafe_constr_of_global`: use `Global.constr_of_global_in_context`
  instead. The returned term contains De Bruijn universe variables. If you don't
  depend on universes being instantiated, simply drop the context.

- `Universes.unsafe_type_of_global`: same as above with
  `Global.type_of_global_in_context`

We changed the type of the following functions:

- `Global.body_of_constant_body`: now also returns the abstract universe context.
  The returned term contains De Bruijn universe variables.

- `Global.body_of_constant`: same as above.

- `Constrinterp.*`: generally, many functions that used to take an
  `evar_map ref` have now been switched to functions that will work in
  a functional way. The old style of passing `evar_map`s as references
  is not supported anymore.

Changes in the abstract syntax tree:

- The practical totality of the AST has been nodified using
  `CAst.t`. This means that all objects coming from parsing will be
  indeed wrapped in a `CAst.t`. `Loc.located` is on its way to
  deprecation. Some minor interfaces changes have resulted from
  this.

We have changed the representation of the following types:

- `Lib.object_prefix` is now a record instead of a nested tuple.

Some tactics and related functions now support static configurability, e.g.:

- `injectable`, `dEq`, etc. take an argument `~keep_proofs` which,
  - if `None`, tells to behave as told with the flag `Keep Proof Equalities`
  - if `Some b`, tells to keep proof equalities iff `b` is true

Declaration of printers for arguments used only in vernac command

- It should now use `declare_extra_vernac_genarg_pprule` rather than
  `declare_extra_genarg_pprule`, otherwise, a failure at runtime might
  happen. An alternative is to register the corresponding argument as
  a value, using `Geninterp.register_val0 wit None`.

Types Alias deprecation and type relocation.

- A few type alias have been deprecated, in all cases the message
  should indicate what the canonical form is.

### STM API

The STM API has seen a general overhaul. The main change is the
introduction of a "Coq document" type, which all operations now take
as a parameter. This effectively functionalize the STM API and will
allow in the future to handle several documents simultaneously.

The main remarkable point is that key implicit global parameters such
as load-paths and required modules are now arguments to the document
creation function. This helps enforcing some key invariants.

### XML IDE Protocol

- Before 8.8, `Query` only executed the first command present in the
 `query` string; starting with 8.8, the caller may include several
 statements. This is useful for instance for temporarily setting an
 option and then executing a command.

## Changes between Coq 8.6 and Coq 8.7

### Ocaml

Coq is compiled with `-safe-string` enabled and requires plugins to do
the same. This means that code using `String` in an imperative way
will fail to compile now. They should switch to `Bytes.t`

Configure supports passing flambda options, use `-flambda-opts OPTS`
with a flambda-enabled Ocaml to tweak the compilation to your taste.

### ML API

- Added two functions for declaring hooks to be executed in reduction
functions when some given constants are traversed:

  * `declare_reduction_effect`: to declare a hook to be applied when some
  constant are visited during the execution of some reduction functions
  (primarily `cbv`).

  * `set_reduction_effect`: to declare a constant on which a given effect
  hook should be called.

- We renamed the following functions:

  ```
  Context.Rel.Declaration.fold   -> Context.Rel.Declaration.fold_constr
  Context.Named.Declaration.fold -> Context.Named.Declaration.fold_constr
  Printer.pr_var_list_decl       -> Printer.pr_compacted_decl
  Printer.pr_var_decl            -> Printer.pr_named_decl
  Nameops.lift_subscript         -> Nameops.increment_subscript
  ```

- We removed the following functions:

  * `Termops.compact_named_context_reverse`: practical substitute is `Termops.compact_named_context`.
  * `Namegen.to_avoid`: equivalent substitute is `Names.Id.List.mem`.

- We renamed the following modules:

  * `Context.ListNamed` -> `Context.Compacted`

- The following type aliases where removed

  * `Context.section_context`: it was just an alias for `Context.Named.t` which is still available.

- The module `Constrarg` was merged into `Stdarg`.

- The following types have been moved and modified:

  * `local_binder` -> `local_binder_expr`
  * `glob_binder` merged with `glob_decl`

- The following constructors have been renamed:

  ```
  LocalRawDef -> CLocalDef
  LocalRawAssum -> CLocalAssum
  LocalPattern -> CLocalPattern
  ```

- In `Constrexpr_ops`:

  Deprecating `abstract_constr_expr` in favor of `mkCLambdaN`, and
  `prod_constr_expr` in favor of `mkCProdN`. Note: the first ones were
  interpreting `(x y z:_)` as `(x:_) (y:_) (z:_)` while the second
  ones were preserving the original sharing of the type.

- In `Nameops`:

  The API has been made more uniform. New combinators added in the
  `Name` space name. Function `out_name` now fails with `IsAnonymous`
  rather than with `Failure "Nameops.out_name"`.

- Location handling and AST attributes:

  Location handling has been reworked. First, `Loc.ghost` has been
  removed in favor of an option type, all objects carrying an optional
  source code location have been switched to use `Loc.t option`.

  Storage of location information has been also refactored. The main
  datatypes representing Coq AST (`constrexpr`, `glob_expr`) have been
  switched to a generic "node with attributes" representation `'a
  CAst.ast`, which is a record of the form:

  ```ocaml
  type 'a ast = private {
    v   : 'a;
    loc : Loc.t option;
    ...
  }
  ```
  consumers of AST nodes are recommended to use accessor-based pattern
  matching `{ v; loc }` to destruct `ast` object. Creation is done
  with `CAst.make ?loc obj`, where the attributes are optional. Some
  convenient combinators are provided in the module. A typical match:

  ```ocaml
  | CCase(loc, a1) -> CCase(loc, f a1)
  ```

  is now done as:
  ```ocaml
  | { v = CCase(a1); loc } -> CAst.make ?loc @@ CCase(f a1)

  ```
  or even better, if plan to preserve the attributes you can wrap your
  top-level function in `CAst.map` to have:

  ```ocaml
  | CCase(a1) -> CCase(f a1)
  ```

  This scheme based on records enables easy extensibility of the AST
  node type without breaking compatibility.

  Not all objects carrying a location have been converted to the
  generic node representation, some of them may be converted in the
  future, for some others the abstraction is not just worth it.

  Thus, we still maintain a `'a Loc.located == Loc.t option * a'`,
  tuple type which should be treated as private datatype (ok to match
  against, but forbidden to manually build), and it is mandatory to
  use it for objects that carry a location. This policy has been
  implemented in the whole code base. Matching a located object hasn't
  changed, however, `Loc.tag ?loc obj` must be used to build one.

- In `GOption`:

  Support for non-synchronous options has been removed. Now all
  options are handled as a piece of normal document state, and thus
  passed to workers, etc... As a consequence, the field
  `Goptions.optsync` has been removed.

- In `Coqlib` / reference location:

  We have removed from Coqlib functions returning `constr` from
  names. Now it is only possible to obtain references, that must be
  processed wrt the particular needs of the client.
  We have changed in constrintern the functions returnin `constr` as
  well to return global references instead.

  Users of `coq_constant/gen_constant` can do
  `Universes.constr_of_global (find_reference dir r)` _however_ note
  the warnings in the `Universes.constr_of_global` in the
  documentation. It is very likely that you were previously suffering
  from problems with polymorphic universes due to using
  `Coqlib.coq_constant` that used to do this. You must rather use
  `pf_constr_of_global` in tactics and `Evarutil.new_global` variants
  when constructing terms in ML (see univpoly.txt for more information).

### Tactic API

- `pf_constr_of_global` now returns a tactic instead of taking a continuation.
  Thus it only generates one instance of the global reference, and it is the
  caller's responsibility to perform a focus on the goal.

- `pf_global`, `construct_reference`, `global_reference`,
  `global_reference_in_absolute_module` now return a `global_reference`
  instead of a `constr`.

- The `tclWEAK_PROGRESS` and `tclNOTSAMEGOAL` tacticals were removed. Their usecase
  was very specific. Use `tclPROGRESS` instead.

- New (internal) tactical `tclINDEPENDENTL` that combined with enter_one allows
  to iterate a non-unit tactic on all goals and access their returned values.

- The unsafe flag of the `Refine.refine` function and its variants has been
  renamed and dualized into typecheck and has been made mandatory.

### Ltac API

Many Ltac specific API has been moved in its own ltac/ folder. Amongst other
important things:

- `Pcoq.Tactic` -> `Pltac`
- `Constrarg.wit_tactic` -> `Tacarg.wit_tactic`
- `Constrarg.wit_ltac` -> `Tacarg.wit_ltac`
- API below `ltac/` that accepted a *`_tactic_expr` now accept a *`_generic_argument`
  instead
- Some printing functions were moved from `Pptactic` to `Pputils`
- A part of `Tacexpr` has been moved to `Tactypes`
- The `TacFun` tactic expression constructor now takes a `Name.t list` for the
  variable list rather than an `Id.t option list`.

The folder itself has been turned into a plugin. This does not change much,
but because it is a packed plugin, it may wreak havoc for third-party plugins
depending on any module defined in the `ltac/` directory. Namely, even if
everything looks OK at compile time, a plugin can fail to load at link time
because it mistakenly looks for a module `Foo` instead of `Ltac_plugin.Foo`, with
an error of the form:

```
Error: while loading myplugin.cmxs, no implementation available for Foo.
```

In particular, most `EXTEND` macros will trigger this problem even if they
seemingly do not use any Ltac module, as their expansion do.

The solution is simple, and consists in adding a statement `open Ltac_plugin`
in each file using a Ltac module, before such a module is actually called. An
alternative solution would be to fully qualify Ltac modules, e.g. turning any
call to Tacinterp into `Ltac_plugin.Tacinterp`. Note that this solution does not
work for `EXTEND` macros though.

### Additional changes in tactic extensions

Entry `constr_with_bindings` has been renamed into
`open_constr_with_bindings`. New entry `constr_with_bindings` now
uses type classes and rejects terms with unresolved holes.

### Error handling

- All error functions now take an optional parameter `?loc:Loc.t`. For
  functions that used to carry a suffix `_loc`, such suffix has been
  dropped.

- `errorlabstrm` and `error` has been removed in favor of `user_err`.

- The header parameter to `user_err` has been made optional.

### Pretty printing

Some functions have been removed, see pretty printing below for more
details.

#### Pretty Printing and XML protocol

The type `std_cmdpps` has been reworked and made the canonical "Coq rich
document type". This allows for a more uniform handling of printing
(specially in IDEs). The main consequences are:

 - Richpp has been confined to IDE use. Most of previous uses of the
   `richpp` type should be replaced now by `Pp.std_cmdpps`. Main API
   has been updated.

 - The XML protocol will send a new message type of `pp`, which should
   be rendered client-wise.

 - `Set Printing Width` is deprecated, now width is controlled
   client-side.

 - `Pp_control` has removed. The new module `Topfmt` implements
   console control for the toplevel.

 - The impure tag system in `Pp` has been removed. This also does away
   with the printer signatures and functors. Now printers tag
   unconditionally.

 - The following functions have been removed from `Pp`:

   ```ocaml
   val stras : int * string -> std_ppcmds
   val tbrk  : int * int -> std_ppcmds
   val tab   : unit -> std_ppcmds
   val pifb  : unit -> std_ppcmds
   val comment  : int -> std_ppcmds
   val comments : ((int * int) * string) list ref
   val eval_ppcmds : std_ppcmds -> std_ppcmds
   val is_empty : std_ppcmds -> bool
   val t : std_ppcmds -> std_ppcmds
   val hb : int -> std_ppcmds
   val vb : int -> std_ppcmds
   val hvb : int -> std_ppcmds
   val hovb : int -> std_ppcmds
   val tb : unit -> std_ppcmds
   val close : unit -> std_ppcmds
   val tclose : unit -> std_ppcmds
   val open_tag : Tag.t -> std_ppcmds
   val close_tag : unit -> std_ppcmds
   val msg_with  : ...

   module Tag
   ```

### Stm API

- We have streamlined the `Stm` API, now `add` and `query` take a
  `coq_parsable` instead a `string` so clients can have more control
  over their input stream. As a consequence, their types have been
  modified.

- The main parsing entry point has also been moved to the
  `Stm`. Parsing is considered a synchronous operation so it will
  either succeed or raise an exception.

- `Feedback` is now only emitted for asynchronous operations. As a
  consequence, it always carries a valid stateid and the type has
  changed to accommodate that.

- A few unused hooks were removed due to cleanups, no clients known.

### Toplevel and Vernacular API

- The components related to vernacular interpretation have been moved
  to their own folder `vernac/` whereas toplevel now contains the
  proper toplevel shell and compiler.

- Coq's toplevel has been ported to directly use the common `Stm`
  API. The signature of a few functions has changed as a result.

### XML Protocol

- The legacy `Interp` call has been turned into a noop.

- The `query` call has been modified, now it carries a mandatory
  `route_id` integer parameter, that associated the result of such
  query with its generated feedback.

## Changes between Coq 8.5 and Coq 8.6

### Parsing

`Pcoq.parsable` now takes an extra optional filename argument so as to
bind locations to a file name when relevant.

### Files

To avoid clashes with OCaml's compiler libs, the following files were renamed:

```
kernel/closure.ml{,i} -> kernel/cClosure.ml{,i}
lib/errors.ml{,i} -> lib/cErrors.ml{,i}
toplevel/cerror.ml{,i} -> toplevel/explainErr.mli{,i}
```

All IDE-specific files, including the XML protocol have been moved to `ide/`

### Reduction functions

In `closure.ml`, we introduced the more precise reduction flags `fMATCH`, `fFIX`,
`fCOFIX`.

We renamed the following functions:

```
Closure.betadeltaiota -> Closure.all
Closure.betadeltaiotanolet -> Closure.allnolet
Reductionops.beta -> Closure.beta
Reductionops.zeta -> Closure.zeta
Reductionops.betaiota -> Closure.betaiota
Reductionops.betaiotazeta -> Closure.betaiotazeta
Reductionops.delta -> Closure.delta
Reductionops.betalet -> Closure.betazeta
Reductionops.betadelta -> Closure.betadeltazeta
Reductionops.betadeltaiota -> Closure.all
Reductionops.betadeltaiotanolet -> Closure.allnolet
Closure.no_red -> Closure.nored
Reductionops.nored -> Closure.nored
Reductionops.nf_betadeltaiota -> Reductionops.nf_all
Reductionops.whd_betadelta -> Reductionops.whd_betadeltazeta
Reductionops.whd_betadeltaiota -> Reductionops.whd_all
Reductionops.whd_betadeltaiota_nolet -> Reductionops.whd_allnolet
Reductionops.whd_betadelta_stack -> Reductionops.whd_betadeltazeta_stack
Reductionops.whd_betadeltaiota_stack -> Reductionops.whd_all_stack
Reductionops.whd_betadeltaiota_nolet_stack -> Reductionops.whd_allnolet_stack
Reductionops.whd_betadelta_state -> Reductionops.whd_betadeltazeta_state
Reductionops.whd_betadeltaiota_state -> Reductionops.whd_all_state
Reductionops.whd_betadeltaiota_nolet_state -> Reductionops.whd_allnolet_state
Reductionops.whd_eta -> Reductionops.shrink_eta
Tacmach.pf_whd_betadeltaiota -> Tacmach.pf_whd_all
Tacmach.New.pf_whd_betadeltaiota -> Tacmach.New.pf_whd_all
```

And removed the following ones:

```
Reductionops.whd_betaetalet
Reductionops.whd_betaetalet_stack
Reductionops.whd_betaetalet_state
Reductionops.whd_betadeltaeta_stack
Reductionops.whd_betadeltaeta_state
Reductionops.whd_betadeltaeta
Reductionops.whd_betadeltaiotaeta_stack
Reductionops.whd_betadeltaiotaeta_state
Reductionops.whd_betadeltaiotaeta
```

In `intf/genredexpr.mli`, `fIota` was replaced by `FMatch`, `FFix` and
`FCofix`. Similarly, `rIota` was replaced by `rMatch`, `rFix` and `rCofix`.

### Notation_ops

Use `Glob_ops.glob_constr_eq` instead of `Notation_ops.eq_glob_constr`.

### Logging and Pretty Printing

* Printing functions have been removed from `Pp.mli`, which is now a
  purely pretty-printing interface. Functions affected are:

```` ocaml
val pp          : std_ppcmds -> unit
val ppnl        : std_ppcmds -> unit
val pperr       : std_ppcmds -> unit
val pperrnl     : std_ppcmds -> unit
val pperr_flush : unit -> unit
val pp_flush    : unit -> unit
val flush_all   : unit -> unit
val msg         : std_ppcmds -> unit
val msgnl       : std_ppcmds -> unit
val msgerr      : std_ppcmds -> unit
val msgerrnl    : std_ppcmds -> unit
val message     : string -> unit
````

  which are no more available. Users of `Pp.pp msg` should now use the
  proper `Feedback.msg_*` function. Clients also have no control over
  flushing, the back end takes care of it.

  Also, the `msg_*` functions now take an optional `?loc` parameter
  for relaying location to the client.

* Feedback related functions and definitions have been moved to the
  `Feedback` module. `message_level` has been renamed to
  level. Functions moved from `Pp` to `Feedback` are:

```` ocaml
val set_logger      : logger -> unit
val std_logger      : logger
val emacs_logger    : logger
val feedback_logger : logger
````

* Changes in the Feedback format/Protocol.

- The `Message` feedback type now carries an optional location, the main
  payload is encoded using the richpp document format.

- The `ErrorMsg` feedback type is thus unified now with `Message` at
  level `Error`.

* We now provide several loggers, `log_via_feedback` is removed in
  favor of `set_logger feedback_logger`. Output functions are:

```` ocaml
val with_output_to_file : string -> ('a -> 'b) -> 'a -> 'b
val msg_error   : ?loc:Loc.t -> Pp.std_ppcmds -> unit
val msg_warning : ?loc:Loc.t -> Pp.std_ppcmds -> unit
val msg_notice  : ?loc:Loc.t -> Pp.std_ppcmds -> unit
val msg_info    : ?loc:Loc.t -> Pp.std_ppcmds -> unit
val msg_debug   : ?loc:Loc.t -> Pp.std_ppcmds -> unit
````

  with the `msg_*` functions being just an alias for `logger $Level`.

* The main feedback functions are:

```` ocaml
val set_feeder : (feedback -> unit) -> unit
val feedback : ?id:edit_or_state_id -> ?route:route_id -> feedback_content -> unit
val set_id_for_feedback : ?route:route_id -> edit_or_state_id -> unit
````
  Note that `feedback` doesn't take two parameters anymore. After
  refactoring the following function has been removed:

```` ocaml
val get_id_for_feedback : unit -> edit_or_state_id * route_id
````

### Kernel API changes

- The interface of the `Context` module was changed.
  Related types and functions were put in separate submodules.
  The mapping from old identifiers to new identifiers is the following:

    ```
    Context.named_declaration            --->  Context.Named.Declaration.t
    Context.named_list_declaration       --->  Context.NamedList.Declaration.t
    Context.rel_declaration              --->  Context.Rel.Declaration.t
    Context.map_named_declaration        --->  Context.Named.Declaration.map_constr
    Context.map_named_list_declaration   --->  Context.NamedList.Declaration.map
    Context.map_rel_declaration          --->  Context.Rel.Declaration.map_constr
    Context.fold_named_declaration       --->  Context.Named.Declaration.fold
    Context.fold_rel_declaration         --->  Context.Rel.Declaration.fold
    Context.exists_named_declaration     --->  Context.Named.Declaration.exists
    Context.exists_rel_declaration       --->  Context.Rel.Declaration.exists
    Context.for_all_named_declaration    --->  Context.Named.Declaration.for_all
    Context.for_all_rel_declaration      --->  Context.Rel.Declaration.for_all
    Context.eq_named_declaration         --->  Context.Named.Declaration.equal
    Context.eq_rel_declaration           --->  Context.Rel.Declaration.equal
    Context.named_context                --->  Context.Named.t
    Context.named_list_context           --->  Context.NamedList.t
    Context.rel_context                  --->  Context.Rel.t
    Context.empty_named_context          --->  Context.Named.empty
    Context.add_named_decl               --->  Context.Named.add
    Context.vars_of_named_context        --->  Context.Named.to_vars
    Context.lookup_named                 --->  Context.Named.lookup
    Context.named_context_length         --->  Context.Named.length
    Context.named_context_equal          --->  Context.Named.equal
    Context.fold_named_context           --->  Context.Named.fold_outside
    Context.fold_named_list_context      --->  Context.NamedList.fold
    Context.fold_named_context_reverse   --->  Context.Named.fold_inside
    Context.instance_from_named_context  --->  Context.Named.to_instance
    Context.extended_rel_list            --->  Context.Rel.to_extended_list
    Context.extended_rel_vect            --->  Context.Rel.to_extended_vect
    Context.fold_rel_context             --->  Context.Rel.fold_outside
    Context.fold_rel_context_reverse     --->  Context.Rel.fold_inside
    Context.map_rel_context              --->  Context.Rel.map_constr
    Context.map_named_context            --->  Context.Named.map_constr
    Context.iter_rel_context             --->  Context.Rel.iter
    Context.iter_named_context           --->  Context.Named.iter
    Context.empty_rel_context            --->  Context.Rel.empty
    Context.add_rel_decl                 --->  Context.Rel.add
    Context.lookup_rel                   --->  Context.Rel.lookup
    Context.rel_context_length           --->  Context.Rel.length
    Context.rel_context_nhyps            --->  Context.Rel.nhyps
    Context.rel_context_tags             --->  Context.Rel.to_tags
    ```

- Originally, rel-context was represented as:

    ```ocaml
    type Context.rel_context = Names.Name.t * Constr.t option * Constr.t
    ```

  Now it is represented as:

    ```ocaml
    type Context.Rel.Declaration.t = LocalAssum of Names.Name.t * Constr.t
                                   | LocalDef of Names.Name.t * Constr.t * Constr.t
    ```

- Originally, named-context was represented as:

    ```ocaml
    type Context.named_context = Names.Id.t * Constr.t option * Constr.t
    ```

  Now it is represented as:

    ```ocaml
    type Context.Named.Declaration.t = LocalAssum of Names.Id.t * Constr.t
                                     | LocalDef of Names.Id.t * Constr.t * Constr.t
    ```

- The various `EXTEND` macros do not handle specially the Coq-defined entries
  anymore. Instead, they just output a name that have to exist in the scope
  of the ML code. The parsing rules (`VERNAC`) `ARGUMENT EXTEND` will look for
  variables `$name` of type `Gram.entry`, while the parsing rules of
  (`VERNAC COMMAND` | `TACTIC`) `EXTEND`, as well as the various `TYPED AS` clauses will
  look for variables `wit_$name` of type `Genarg.genarg_type`. The small DSL
  for constructing compound entries still works over this scheme. Note that in
  the case of (`VERNAC`) `ARGUMENT EXTEND`, the name of the argument entry is bound
  in the parsing rules, so beware of recursive calls.
  
  For example, to get `wit_constr` you must `open Constrarg` at the top of the file.

- `Evarutil` was split in two parts. The new `Evardefine` file exposes functions
  `define_evar_`* mostly used internally in the unification engine.

- The `Refine` module was moved out of `Proofview`.

    ```
    Proofview.Refine.* --->  Refine.*
    ```

- A statically monotonic evarmap type was introduced in `Sigma`. Not all the API
  has been converted, so that the user may want to use compatibility functions
  `Sigma.to_evar_map` and `Sigma.Unsafe.of_evar_map` or `Sigma.Unsafe.of_pair` when
  needed. Code can be straightforwardly adapted in the following way:

  ```ocaml
  let (sigma, x1) = ... in
  ...
  let (sigma, xn) = ... in
  (sigma, ans)
  ```

  should be turned into:

  ```ocaml
  open Sigma.Notations

  let Sigma (x1, sigma, p1) = ... in
  ...
  let Sigma (xn, sigma, pn) = ... in
  Sigma (ans, sigma, p1 +> ... +> pn)
  ```
  
  Examples of `Sigma.Unsafe.of_evar_map` include:
  
  ```
  Evarutil.new_evar env (Tacmach.project goal) ty   ----> Evarutil.new_evar env (Sigma.Unsafe.of_evar_map (Tacmach.project goal)) ty
  ```

- The `Proofview.Goal.`*`enter` family of functions now takes a polymorphic
  continuation given as a record as an argument.

  ```ocaml
  Proofview.Goal.enter begin fun gl -> ... end
  ```

  should be turned into

  ```ocaml
  open Proofview.Notations

  Proofview.Goal.enter { enter = begin fun gl -> ... end }
  ```
  
- `Tacexpr.TacDynamic(Loc.dummy_loc, Pretyping.constr_in c)`      ---> `Tacinterp.Value.of_constr c`
- `Vernacexpr.HintsResolveEntry(priority, poly, hnf, path, atom)` ---> `Vernacexpr.HintsResolveEntry(Vernacexpr.({hint_priority = priority; hint_pattern = None}), poly, hnf, path, atom)`
- `Pretyping.Termops.mem_named_context`                           ---> `Engine.Termops.mem_named_context_val`
- `Global.named_context`                                         ---> `Global.named_context_val`
- `Context.Named.lookup`                                         ---> `Environ.lookup_named_val`

### Search API

The main search functions now take a function iterating over the
results. This allows for clients to use streaming or more economic
printing.

### XML Protocol

- In several places, flat text wrapped in `<string>` tags now appears as structured text inside `<richpp>` tags.

- The "errormsg" feedback has been replaced by a "message" feedback which contains `<feedback\_content>` tag, with a message_level attribute of "error".

## Changes between Coq 8.4 and Coq 8.5

### Refactoring : more mli interfaces and simpler grammar.cma

- A new directory intf/ now contains mli-only interfaces :

  * `Constrexpr` : definition of `constr_expr`, was in `Topconstr`
  * `Decl_kinds` : now contains `binding_kind = Explicit | Implicit`
  * `Evar_kinds` : type `Evar_kinds.t` was previously `Evd.hole_kind`
  * `Extend` : was `parsing/extend.mli`
  * `Genredexpr` : regroup `Glob_term.red_expr_gen` and `Tacexpr.glob_red_flag`
  * `Glob_term`  : definition of `glob_constr`
  * `Locus` : definition of occurrences and stuff about clauses
  * `Misctypes` : `intro_pattern_expr`, `glob_sort`, `cast_type`, `or_var`, ...
  * `Notation_term` : contains `notation_constr`, was `Topconstr.aconstr`
  * `Pattern` : contains `constr_pattern`
  * `Tacexpr` : was `tactics/tacexpr.ml`
  * `Vernacexpr` : was `toplevel/vernacexpr.ml`

- Many files have been divided :

  * vernacexpr: vernacexpr.mli + Locality
  * decl_kinds: decl_kinds.mli + Kindops
  * evd: evar_kinds.mli + evd
  * tacexpr: tacexpr.mli + tacops
  * glob_term: glob_term.mli + glob_ops + genredexpr.mli + redops
  * topconstr: constrexpr.mli + constrexpr_ops
              + notation_expr.mli + notation_ops + topconstr
  * pattern: pattern.mli + patternops
  * libnames: libnames (qualid, reference) + globnames (global_reference)
  * egrammar: egramml + egramcoq

- New utility files : miscops (cf. misctypes.mli) and
  redops (cf genredexpr.mli).

- Some other directory changes :
  * grammar.cma and the source files specific to it are now in grammar/
  * pretty-printing files are now in printing/

- Inner-file changes :

  * aconstr is now notation_constr, all constructors for this type
    now start with a N instead of a A (e.g. NApp instead of AApp),
    and functions about aconstr may have been renamed (e.g. match_aconstr
    is now match_notation_constr).

  * occurrences (now in Locus.mli) is now an algebraic type, with
    - AllOccurrences instead of all_occurrences_expr = (false,[])
    - (AllOccurrencesBut l) instead of (all_occurrences_expr_but l) = (false,l)
    - NoOccurrences instead of no_occurrences_expr = (true,[])
    - (OnlyOccurrences l) instead of (no_occurrences_expr_but l) = (true,l)

  * move_location (now in Misctypes) has two new constructors
    MoveFirst and MoveLast replacing (MoveToEnd false) and (MoveToEnd true)

- API of pretyping.ml and constrintern.ml has been made more uniform
  * Parametrization of understand_* functions is now made using
    "inference flags"
  * Functions removed:
    - interp_constr_judgment (inline its former body if really needed)
    - interp_casted_constr, interp_type: use instead interp_constr with
      expected_type set to OfType or to IsType
    - interp_gen: use any of interp_constr, interp_casted_constr, interp_type
    - interp_open_constr_patvar
    - interp_context: use interp_context_evars (with a "evar_map ref") and
      call solve_remaining_evars afterwards with a failing flag
      (e.g. all_and_fail_flags)
    - understand_type, understand_gen: use understand with appropriate
      parameters
  * Change of semantics:
    - Functions interp_*_evars_impls have a different interface and do
      not any longer check resolution of evars by default; use
      check_evars_are_solved explicitly to check that evars are solved.
  See also the corresponding commit log.

- Tactics API: new_induct -> induction; new_destruct -> destruct;
  letin_pat_tac do not accept a type anymore

- New file find_subterm.ml for gathering former functions
  `subst_closed_term_occ_modulo`, `subst_closed_term_occ_decl` (which now
  take and outputs also an `evar_map`), and
  `subst_closed_term_occ_modulo`, `subst_closed_term_occ_decl_modulo` (now
  renamed into `replace_term_occ_modulo` and
  `replace_term_occ_decl_modulo`).

- API of Inductiveops made more uniform (see commit log or file itself).

- API of intros_pattern style tactic changed; "s" is dropped in
  "intros_pattern" and "intros_patterns" is not anymore behaving like
  tactic "intros" on the empty list.

- API of cut tactics changed: for instance, cut_intro should be replaced by
  "assert_after Anonymous"

- All functions taking an env and a sigma (or an evdref) now takes the
  env first.

## Changes between Coq 8.3 and Coq 8.4

- Functions in unification.ml have now the evar_map coming just after the env

- Removal of Tacinterp.constr_of_id

Use instead either global_reference or construct_reference in constrintern.ml.

- Optimizing calls to Evd functions

Evars are split into defined evars and undefined evars; for
efficiency, when an evar is known to be undefined, it is preferable to
use specific functions about undefined evars since these ones are
generally fewer than the defined ones.

- Type changes in TACTIC EXTEND rules

Arguments bound with tactic(_) in TACTIC EXTEND rules are now of type
glob_tactic_expr, instead of glob_tactic_expr * tactic. Only the first
component is kept, the second one can be obtained via
Tacinterp.eval_tactic.

- ARGUMENT EXTEND

It is now forbidden to use TYPED simultaneously with {RAW,GLOB}_TYPED
in ARGUMENT EXTEND statements.

- Renaming of rawconstr to glob_constr

The "rawconstr" type has been renamed to "glob_constr" for
consistency. The "raw" in everything related to former rawconstr has
been changed to "glob". For more details about the rationale and
scripts to migrate code using Coq's internals, see commits 13743,
13744, 13755, 13756, 13757, 13758, 13761 (by glondu, end of December
2010) in Subversion repository. Contribs have been fixed too, and
commit messages there might also be helpful for migrating.

## Changes between Coq 8.2 and Coq 8.3

### Light cleaning in evaruil.ml

whd_castappevar is now whd_head_evar
obsolete whd_ise disappears

### Restructuration of the syntax of binders

```
binders_let -> binders
binders_let_fixannot -> binders_fixannot
binder_let -> closed_binder (and now covers only bracketed binders)
binder was already obsolete and has been removed
```

### Semantical change of h_induction_destruct

Warning, the order of the isrec and evar_flag was inconsistent and has
been permuted. Tactic induction_destruct in tactics.ml is unchanged.

### Internal tactics renamed

There is no more difference between bindings and ebindings. The
following tactics are therefore renamed

```
apply_with_ebindings_gen -> apply_with_bindings_gen
left_with_ebindings -> left_with_bindings
right_with_ebindings -> right_with_bindings
split_with_ebindings -> split_with_bindings
```

and the following tactics are removed

 - apply_with_ebindings (use instead apply_with_bindings)
 - eapply_with_ebindings (use instead eapply_with_bindings)

### Obsolete functions in typing.ml

For mtype_of, msort_of, mcheck, now use type_of, sort_of, check

### Renaming functions renamed

```
concrete_name -> compute_displayed_name_in
concrete_let_name -> compute_displayed_let_name_in
rename_rename_bound_var -> rename_bound_vars_as_displayed
lookup_name_as_renamed -> lookup_name_as_displayed
next_global_ident_away true -> next_ident_away_in_goal
next_global_ident_away false -> next_global_ident_away
```

### Cleaning in commmand.ml

Functions about starting/ending a lemma are in lemmas.ml
Functions about inductive schemes are in indschemes.ml

Functions renamed:

```
declare_one_assumption -> declare_assumption
declare_assumption -> declare_assumptions
Command.syntax_definition -> Metasyntax.add_syntactic_definition
declare_interning_data merged with add_notation_interpretation
compute_interning_datas -> compute_full_internalization_env
implicits_env -> internalization_env
full_implicits_env -> full_internalization_env
build_mutual -> do_mutual_inductive
build_recursive -> do_fixpoint
build_corecursive -> do_cofixpoint
build_induction_scheme -> build_mutual_induction_scheme
build_indrec -> build_induction_scheme
instantiate_type_indrec_scheme -> weaken_sort_scheme
instantiate_indrec_scheme -> modify_sort_scheme
make_case_dep, make_case_nodep -> build_case_analysis_scheme
make_case_gen -> build_case_analysis_scheme_default
```

Types:

decl_notation -> decl_notation option

### Cleaning in libnames/nametab interfaces

Functions:

```
dirpath_prefix -> pop_dirpath
extract_dirpath_prefix pop_dirpath_n
extend_dirpath -> add_dirpath_suffix
qualid_of_sp -> qualid_of_path
pr_sp -> pr_path
make_short_qualid -> qualid_of_ident
sp_of_syntactic_definition -> path_of_syntactic_definition 
sp_of_global -> path_of_global
id_of_global -> basename_of_global
absolute_reference -> global_of_path
locate_syntactic_definition -> locate_syndef
path_of_syntactic_definition -> path_of_syndef
push_syntactic_definition -> push_syndef
```

Types:

section_path -> full_path

### Cleaning in parsing extensions (commit 12108)

Many moves and renamings, one new file (Extrawit, that contains wit_tactic).

### Cleaning in tactical.mli

```
tclLAST_HYP -> onLastHyp
tclLAST_DECL -> onLastDecl
tclLAST_NHYPS -> onNLastHypsId
tclNTH_DECL -> onNthDecl
tclNTH_HYP -> onNthHyp
onLastHyp -> onLastHypId
onNLastHyps -> onNLastDecls
onClauses -> onClause
allClauses -> allHypsAndConcl
```

and removal of various unused combinators on type "clause"

## Changes between Coq 8.1 and Coq 8.2

### Datatypes

List of occurrences moved from "int list" to "Termops.occurrences" (an
  alias to "bool * int list")
ETIdent renamed to ETName

### Functions

```
Eauto: e_resolve_constr, vernac_e_resolve_constr -> simplest_eapply
Tactics: apply_with_bindings -> apply_with_bindings_wo_evars
Eauto.simplest_apply -> Hiddentac.h_simplest_apply
Evarutil.define_evar_as_arrow -> define_evar_as_product
Old version of Tactics.assert_tac disappears
Tactics.true_cut renamed into Tactics.assert_tac
Constrintern.interp_constrpattern -> intern_constr_pattern
Hipattern.match_with_conjunction is a bit more restrictive
Hipattern.match_with_disjunction is a bit more restrictive
```

### Universe names (univ.mli)

 ```ocaml
 base_univ -> type0_univ  (* alias of Set is the Type hierarchy *)
 prop_univ -> type1_univ  (* the type of Set in the Type hierarchy *)
 neutral_univ -> lower_univ (* semantic alias of Prop in the Type hierarchy *)
 is_base_univ -> is_type1_univ
 is_empty_univ -> is_lower_univ
 ```

### Sort names (term.mli)

  ```
  mk_Set -> set_sort
  mk_Prop -> prop_sort
  type_0 -> type1_sort
  ```

## Changes between Coq 8.0 and Coq 8.1

### Functions

- Util: option_app -> option_map
- Term: substl_decl -> subst_named_decl
- Lib: library_part -> remove_section_part
- Printer: prterm -> pr_lconstr
- Printer: prterm_env -> pr_lconstr_env
- Ppconstr: pr_sort -> pr_rawsort
- Evd: in_dom, etc got standard ocaml names (i.e. mem, etc)
- Pretyping:
   - understand_gen_tcc and understand_gen_ltac merged into understand_ltac
   - type_constraints can now say typed by a sort (use OfType to get the
     previous behavior)
- Library: import_library -> import_module

### Constructors

 * Declarations: mind_consnrealargs -> mind_consnrealdecls
 * NoRedun -> NoDup
 * Cast and RCast have an extra argument: you can recover the previous
  behavior by setting the extra argument to "CastConv DEFAULTcast" and
  "DEFAULTcast" respectively
 * Names: "kernel_name" is now "constant" when argument of Term.Const
 * Tacexpr: TacTrueCut and TacForward(false,_,_) merged into new TacAssert
 * Tacexpr: TacForward(true,_,_) branched to TacLetTac

### Modules

 * module Decl_kinds: new interface
 * module Bigint: new interface
 * module Tacred spawned module Redexpr
 * module Symbols -> Notation
 * module Coqast, Ast, Esyntax, Termast, and all other modules related to old
   syntax are removed
 * module Instantiate: integrated to Evd
 * module Pretyping now a functor: use Pretyping.Default instead

### Internal names

OBJDEF and OBJDEF1 -> CANONICAL-STRUCTURE

### Tactic extensions

 * printers have an extra parameter which is a constr printer at high precedence
 *  the tactic printers have an extra arg which is the expected precedence
 *  level is now a precedence in declare_extra_tactic_pprule
 * "interp" functions now of types the actual arg type, not its encapsulation
    as a generic_argument

## Changes between Coq 7.4 and Coq 8.0

See files in dev/syntax-v8


## Main changes between Coq 7.4 and Coq 8.0

### Changes due to introduction of modules

#### Kernel

  The module level has no effect on constr except for the structure of
section_path. The type of unique names for constructions (what
section_path served) is now called a kernel name and is defined by
 
```ocaml
type uniq_ident = int * string * dir_path (* int may be enough *)
type module_path =
  | MPfile of dir_path    (* reference to physical module, e.g. file *)
  | MPbound of uniq_ident (* reference to a module parameter in a functor *)
  | MPself of uniq_ident  (* reference to one of the containing module *)
  | MPdot of module_path * label
type label = identifier
type kernel_name = module_path * dir_path * label
                   ^^^^^^^^^^^   ^^^^^^^^   ^^^^^
                        |           |         \
                        |           |          the base name
                        |           \
                       /             the (true) section path
   example:                          (non empty only inside open sections)
   L = (* i.e. some file of logical name L *)
   struct
     module A = struct Def a = ... end
   end
   M = (* i.e. some file of logical name M *)
   struct
     Def t = ...
     N = functor (X : sig module T = struct Def b = ... end end) -> struct
       module O = struct
         Def u = ...
       end
       Def x := ... <M>.t ... <N>.O.u ... X.T.b ... L.A.a
```

   <M> and <N> are self-references, X is a bound reference and L is a
reference to a physical module.
 
  Notice that functor application is not part of a path: it must be
named by a "module M = F(A)" declaration to be used in a kernel
name.
 
  Notice that Jacek chose a practical approach, making directories not
modules. Another approach could have been to replace the constructor
MPfile by a constant constructor MProot representing the root of the
world.
 
  Other relevant informations are in kernel/entries.ml (type
module_expr) and kernel/declarations.ml (type module_body and
module_type_body).                                                              

#### Library

1. tables
[Summaries] - the only change is the special treatment of the
global environmet.

2. objects 
[Libobject] declares persistent objects, given with methods:

   * cache_function specifying how to add the object in the current
       scope;
   * load_function, specifying what to do when the module 
       containing the object is loaded; 
   * open_function, specifying what to do when the module 
       containing the object is opened (imported);
   * classify_function, specyfying what to do with the object,
       when the current module (containing the object) is ended. 
   * subst_function
   * export_function, to signal end_section survival

(Almost) Each of these methods is called with a parameter of type
object_name = section_path * kernel_name
where section_path is the full user name of the object (such as
Coq.Init.Datatypes.Fst) and kernel_name is its substitutive internal
version such as (MPself<Datatypes#1>,[],"Fst") (see above)


#### What happens at the end of an interactive module ?

(or when a file is stored and reloaded from disk)

All summaries (except Global environment) are reverted to the state
from before the beginning of the module, and:

1. the objects (again, since last Declaremods.start_module or
   Library.start_library) are classified using the classify_function.
   To simplify consider only those who returned Substitute _ or Keep _.

2. If the module is not a functor, the subst_function for each object of
   the first group is called with the substitution 
   [MPself "<Datatypes#1>" |-> MPfile "Coq.Init.Datatypes"].
   Then the load_function is called for substituted objects and the
   "keep" object. 
   (If the module is a library the substitution is done at reloading).

3. The objects which returned substitute are stored in the modtab
   together with the self ident of the module, and functor argument
   names if the module was a functor.

   They will be used (substituted and loaded) when a command like 
     Module M := F(N)    or
     Module Z := N 
   is evaluated


#### The difference between "substitute" and "keep" objects

1. The "keep" objects can _only_ reference other objects by section_paths
and qualids. They do not need the substitution function.

They will work after end_module (or reloading a compiled library),
because these operations do not change section_path's

They will obviously not work after Module Z:=N.
 
These would typically be grammar rules, pretty printing rules etc.



2. The "substitute" objects can _only_ reference objects by
kernel_names. They must have a valid subst_function. 

They will work after end_module _and_ after Module Z:=N or 
Module Z:=F(M).



Other kinds of objects:

3. "Dispose" - objects which do not survive end_module
     As a consequence, objects which reference other objects sometimes
     by kernel_names and sometimes by section_path must be of this kind...

4. "Anticipate" - objects which must be treated individually by
    end_module (typically "REQUIRE" objects)



#### Writing subst_thing functions

The subst_thing shoud not copy the thing if it hasn't actually
changed. There are some cool emacs macros in dev/objects.el 
to help writing subst functions this way quickly and without errors.
Also there are *_smartmap functions in Util.

The subst_thing functions are already written for many types,
including constr (Term.subst_mps), 
global_reference (Libnames.subst_global),
rawconstr (Rawterm.subst_raw) etc

They are all (apart from constr, for now) written in the non-copying
way.


#### Nametab

Nametab has been made more uniform. For every kind of thing there is
only one "push" function and one "locate" function. 


#### Lib

library_segment is now a list of object_name * library_item, where
object_name = section_path * kernel_name (see above)

New items have been added for open modules and module types


#### Declaremods

Functions to declare interactive and noninteractive modules and module
types.


#### Library

Uses Declaremods to actually communicate with Global and to register
objects.


### Other changes

Internal representation of tactics bindings has changed (see type
Rawterm.substitution).

New parsing model for tactics and vernacular commands

  - Introduction of a dedicated type for tactic expressions
    (Tacexpr.raw_tactic_expr)
  - Introduction of a dedicated type for vernac expressions
    (Vernacexpr.vernac_expr)
  - Declaration of new vernacular parsing rules by a new camlp4 macro
    GRAMMAR COMMAND EXTEND ... END  to be used in ML files
  - Declaration of new tactics parsing/printing rules by a new camlp4 macro
    TACTIC EXTEND ... END  to be used in ML files

New organisation of THENS:

- tclTHENS tac tacs : tacs is now an array
- tclTHENSFIRSTn tac1 tacs tac2 :
  apply tac1 then, apply the array tacs on the first n subgoals and
  tac2 on the remaining subgoals (previously tclTHENST)
- tclTHENSLASTn tac1 tac2 tacs :
  apply tac1 then, apply tac2 on the first subgoals and apply the array
  tacs on the last n subgoals
- tclTHENFIRSTn tac1 tacs = tclTHENSFIRSTn tac1 tacs tclIDTAC (prev. tclTHENSI)
- tclTHENLASTn tac1 tacs  = tclTHENSLASTn tac1 tclIDTAC tacs
- tclTHENFIRST tac1 tac2  = tclTHENFIRSTn tac1 [|tac2|]
- tclTHENLAST tac1 tac2   = tclTHENLASTn tac1 [|tac2|] (previously tclTHENL)
- tclTHENS tac1 tacs = tclTHENSFIRSTn tac1 tacs (fun _ -> error "wrong number")
- tclTHENSV same as tclTHENS but with an array
- tclTHENSi : no longer available

Proof_type: subproof field in type proof_tree glued with the ref field

Tacmach: no more echo from functions of module Refiner

Files plugins/*/g_*.ml4 take the place of files plugins/*/*.v.

Files parsing/{vernac,tac}extend.ml{4,i} implements TACTIC EXTEND andd
  VERNAC COMMAND EXTEND macros

File syntax/PPTactic.v moved to parsing/pptactic.ml

Tactics about False and not now in tactics/contradiction.ml

Tactics depending on Init now tactics/*.ml4 (no longer in tactics/*.v)

File tacinterp.ml moved from proofs to directory tactics


## Changes between Coq 7.1 and Coq 7.2

The core of Coq (kernel) has meen minimized with the following effects:

- kernel/term.ml      split into kernel/term.ml,      pretyping/termops.ml
- kernel/reduction.ml split into kernel/reduction.ml, pretyping/reductionops.ml
- kernel/names.ml     split into kernel/names.ml,     library/nameops.ml
- kernel/inductive.ml split into kernel/inductive.ml, pretyping/inductiveops.ml

the prefixes "Is" ans "IsMut" have been dropped from kind_of_term constructors,
e.g. IsRel is now Rel, IsMutCase is now Case, etc.
