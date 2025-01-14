# Beginner's guide to hacking Rocq

## Getting dependencies

See the first section of [`INSTALL.md`](../../INSTALL.md).  Developers are
recommended to use a recent OCaml version, which they can get through
opam or Nix, in particular.

## Configuring Dune caching and default verbosity

There are several configuration settings that you can control globally
by creating a Dune configuration file (see `man dune-config` to learn
more). This file is generally located in `~/.config/dune/config` (this
is system-dependent). It should start with the version of the Dune
language used (by the configuration file---which can be different from
the one used in the Rocq repository), e.g.:

```
(lang dune 2.0)
```

- You will get faster rebuilds if you enable Dune caching. This is
  true in all cases, but even more so when using the targets in
  `Makefile` (see below).

  To set up Dune caching, you should append the following line to your
  Dune configuration file:

  ```
  (cache enabled)
  ```

  Note that by default, Dune caching will use up to 10GB of disk size.
  See the [official documentation](https://dune.readthedocs.io/en/stable/caching.html#on-disk-size)
  to learn how to change the default.

- Dune is not very verbose by default. If you want to change the
  behavior to a more verbose one, you may append the following line to
  your Dune configuration file:

  ```
  (display short)
  ```

## Building `rocq` binary

We recommend that you use the targets in the `Makefile`. Calling `make` will
show the available targets. See [`build-system.dune.md`](build-system.dune.md)
to learn more about them.

```
$ git clone https://github.com/coq/coq.git
$ cd coq
$ make
    # to get an idea of the available targets
$ make check
   # build all OCaml files as fast as possible
$ dune exec -- dev/shim/coqc-prelude test.v
    # update coqc and the prelude and compile file test.v
$ make world
    # build coq and the complete stdlib and setup it for use under _build/install/default
    # In particular, you may run, e.g., coq_makefile from _build/install/default
    # to build some test project
```

When running the commands above, you may set `DUNEOPT=--display=short`
for a more verbose build (not required if you have already set the
default verbosity globally as described in the previous section).

To learn how to run the test suite, you can read
[`test-suite/README.md`](../../test-suite/README.md).

## Rocq functions of interest
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

When using `rlwrap rocq repl` make sure the version of `rlwrap` is at least
`0.42`, otherwise you will get

```
rlwrap: error: Couldn't read completions from /usr/share/rlwrap/completions/coqtop: No such file or directory
```

If this happens either update or use an alternate readline wrapper like `ledit`.
