# Beginner's guide to hacking Coq

## Getting dependencies

See the first section of [`INSTALL`](../../INSTALL).  Developers are
recommended to use a recent OCaml version, which they can get through
opam or Nix, in particular.

## Building `coqtop` / `coqc` binaries

We recommend that you use the targets in `Makefile.dune`.  See
[`build-system.dune.md`](build-system.dune.md) to learn more about
them.  In the example below, you may omit `-f Makefile.dune` by
setting `COQ_USE_DUNE=1`.

```
$ git clone https://github.com/coq/coq.git
$ cd coq
$ make -f Makefile.dune
    # to get an idea of the available targets
$ make -f Makefile.dune check
   # build all OCaml files as fast as possible
$ dune exec -- dev/shim/coqc-prelude test.v
    # update coqc and the prelude and compile file test.v
$ make -f Makefile.dune world
    # build coq and the complete stdlib and setup it for use under _build/install/default
    # In particular, you may run, e.g., coq_makefile from _build/install/default
    # to build some test project
```

Alternatively, you can use the legacy build system (which is now
a hybrid since it relies on Dune for the OCaml parts). If you haven't
set `COQ_USE_DUNE=1`, then you don't need `-f Makefile.make`.

```
$ ./configure -profile devel
    # add -warn-error no if you don't want to fail on warnings while building the stlib
$ make -f Makefile.make -j $JOBS
    # Make once for `merlin` (autocompletion tool)

<hack>

$ make -f Makefile.make -j $JOBS states
    # builds just enough to run coqtop
$ bin/coqc <test_file_name.v>
<goto hack until stuff works>
```

To learn how to run the test suite, you can read
[`test-suite/README.md`](../../test-suite/README.md).

## Coq functions of interest
- `Coqtop.start`: This function is the main entry point of coqtop.
- `Coqtop.parse_args `: This function is responsible for parsing command-line arguments.
- `Coqloop.loop`: This function implements the read-eval-print loop.
- `Vernacentries.interp`: This function is called to execute the Vernacular command user have typed.
                       It dispatches the control to specific functions handling different Vernacular command.
- `Vernacentries.vernac_check_may_eval`: This function handles the `Check ...` command.


## Development environment + tooling

- [`Merlin`](https://github.com/ocaml/merlin) for autocomplete.
- [Wiki pages on tooling containing `emacs`, `vim`, and `git` information](https://github.com/coq/coq/wiki/DevelSetup)
- [`ocamlformat`](https://github.com/ocaml-ppx/ocamlformat) provides
  support for automatic formatting of OCaml code. To use it please run
  `dune build @fmt`, see `ocamlformat`'s documentation for more help.

## A note about rlwrap

When using `rlwrap coqtop` make sure the version of `rlwrap` is at least
`0.42`, otherwise you will get

```
rlwrap: error: Couldn't read completions from /usr/share/rlwrap/completions/coqtop: No such file or directory
```

If this happens either update or use an alternate readline wrapper like `ledit`.
