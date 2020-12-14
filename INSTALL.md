Installing From Sources
=======================

This document presents instructions to install this branch of Coq.
For more general installation instructions and information about known
build system issues, please consult the wiki page: 

  https://github.com/coq/coq/wiki#coq-installation

Build Requirements
------------------

To compile Coq yourself, you need:

- [OCaml](https://ocaml.org/) (version >= 4.05.0)
  (This version of Coq has been tested up to OCaml 4.11.1)

- The [ZArith library](https://github.com/ocaml/Zarith) >= 1.10

- The [findlib](http://projects.camlcity.org/projects/findlib.html) library (version >= 1.8.0)

- GNU Make (version >= 3.81)

- a C compiler

- an IEEE-754 compliant architecture with rounding to nearest
  ties to even as default rounding mode (most architectures
  should work nowadays)

- for CoqIDE, the
  [lablgtk3-sourceview3](https://github.com/garrigue/lablgtk) library
  (version >= 3.1.0), and the corresponding GTK 3.x libraries, as
  of today (gtk+3 >= 3.18 and gtksourceview3 >= 3.18)

Primitive floating-point numbers require IEEE-754 compliance
(`Require Import Floats`). Common sources of incompatibility
are checked at configure time, preventing compilation. In the
unlikely event an incompatibility remains undetected, using `Floats`
would enable proving `False` on this architecture.

Note that OCaml dependencies (`zarith` and `lablgtk3-sourceview3` at
this moment) must be properly registered with `findlib/ocamlfind`
since Coq's build system uses `findlib` to locate them.

Debian / Ubuntu users can get the necessary system packages for
CoqIDE with:

    $ sudo apt-get install libgtksourceview-3.0-dev

Opam (https://opam.ocaml.org/) is recommended to install OCaml and
the corresponding packages.

    $ opam switch create coq 4.11.1+flambda
    $ eval $(opam env)
    $ opam install ocamlfind zarith lablgtk3-sourceview3

should get you a reasonable OCaml environment to compile Coq. See the
OPAM documentation for more help.

Nix users can also get all the required dependencies by running:

    $ nix-shell

Advanced users may want to experiment with the OCaml Flambda
compiler as way to improve the performance of Coq. In order to
profit from Flambda, a special build of the OCaml compiler that has
the Flambda optimizer enabled must be installed. For OPAM users,
this amounts to installing a compiler switch ending in `+flambda`,
such as `4.07.1+flambda`. For other users, YMMV. Once `ocamlopt -config`
reports that Flambda is available, some further optimization options
can be used; see the entry about `-flambda-opts` in the build guide
for more details.

Build and Installation Procedure
--------------------------------

Coq offers the choice of two build systems, an experimental one based
on [Dune](https://github.com/ocaml/dune), and the standard
makefile-based one.

Please see [INSTALL.make.md](dev/doc/INSTALL.make.md) for build and
installation instructions using `make`. If you wish to experiment with
the Dune-based system see the [dune guide for
developers](dev/doc/build-system.dune.md).

Run-time dependencies of native compilation
-------------------------------------------

The OCaml compiler and findlib are build-time dependencies, but also
run-time dependencies if you wish to use the native compiler.

OCaml toolchain advisory
------------------------

When loading plugins or `vo` files, you should make sure that these
were compiled with the same OCaml setup (version, flags,
dependencies...) as Coq.  Distribution of pre-compiled plugins and
`.vo` files is only possible if users are guaranteed to have the same
Coq version compiled with the same OCaml toolchain.  An OCaml setup
mismatch is the most probable cause for an `Error while loading ...:
implementation mismatch on ...`.

coq_environment.txt
-------------------
Coq binaries which honor environment variables, such as `COQLIB`, can
be seeded values for these variables by placing a text file named
`coq_environment.txt` next to them. The file can contain assignments
like `COQLIB="some path"`, that is a variable name followed by `=` and
a string that follows OCaml's escaping conventions. This feature can be
used by installers of binary package to make Coq aware of its installation
path.
