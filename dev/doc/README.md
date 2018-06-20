# Beginner's guide to hacking Coq

## Getting dependencies

Assuming one is running Ubuntu (if not, replace `apt` with the package manager of choice)

```
$ sudo apt-get install make opam git

# At the time of writing, <latest-ocaml-version> is 4.07.0.
# The latest version number is available at: https://ocaml.org/releases/

$ opam init --comp <latest-ocaml-version>

# Then follow the advice displayed at the end as how to update your
  ~/.bashrc and ~/.ocamlinit files.

$ source ~/.bashrc
$ opam install camlp5

# needed if you want to build "coqide" target

$ sudo apt-get install liblablgtksourceview2-ocaml-dev \
  libgtk2.0-dev libgtksourceview2.0-dev
$ opam install lablgtk
```

## Building `coqtop`
The general workflow is to first setup a development environment with
the correct `configure` settings, then hacking on Coq, make-ing, and testing.


This document will use `$JOBS` to refer to the number of parallel jobs one
is willing to have with `make`.


```
$ git clone git clone https://github.com/coq/coq.git
$ cd coq
$ ./configure -profile devel
$ make -j $JOBS # Make once for `merlin`(autocompletion tool)

<hack>

$ make -j $JOBS states # builds just enough to run coqtop
$ bin/coqtop -compile <test_file_name.v>
<goto hack until stuff works>

<run test-suite>
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

## A note about rlwrap

When using `rlwrap coqtop` make sure the version of `rlwrap` is at least
`0.42`, otherwise you will get

```
rlwrap: error: Couldn't read completions from /usr/share/rlwrap/completions/coqtop: No such file or directory
```

If this happens either update or use an alternate readline wrapper like `ledit`.
