Installing From Sources
=======================

To install and use Rocq, we recommend relying on [the Rocq
platform](https://github.com/coq/platform/) or on a package manager
(e.g. opam or Nix).

See https://coq.inria.fr/download and
https://github.com/coq/coq/wiki#coq-installation to learn more.

If you need to build Rocq from sources manually (e.g. to
contribute to Rocq or to write a Rocq package), the remainder of this
file explains how to do so.

Build Requirements
------------------

To compile Rocq yourself, you need:

- [OCaml](https://ocaml.org/) (version >= 4.09.0)
  (This version of Rocq has been tested up to OCaml 4.14.1, for the 4.x series)

  Support for OCaml 5.x remains experimental.

- The [Dune OCaml build system](https://github.com/ocaml/dune/) >= 3.8

- The [ZArith library](https://github.com/ocaml/Zarith) >= 1.11

- The [findlib](http://projects.camlcity.org/projects/findlib.html) library (version >= 1.8.1)

- a C compiler

- an IEEE-754 compliant architecture with rounding to nearest
  ties to even as default rounding mode (most architectures
  should work nowadays)

- for RocqIDE, the
  [lablgtk3-sourceview3](https://github.com/garrigue/lablgtk) library
  (version >= 3.1.2), and the corresponding GTK 3.x libraries, as
  of today (gtk+3 >= 3.18 and gtksourceview3 >= 3.18)

- [optional] GNU Make (version >= 3.81)

See [below](#Known-Problems) for a discussion of platform-specific
issues with dependencies.

Primitive floating-point numbers require IEEE-754 compliance
(`Require Import Floats`). Common sources of incompatibility
are checked at configure time, preventing compilation. In the
unlikely event an incompatibility remains undetected, using `Floats`
would enable proving `False` on this architecture.

Note that OCaml dependencies (`zarith` and `lablgtk3-sourceview3` at
this moment) must be properly registered with `findlib/ocamlfind`
since Rocq's build system uses `findlib` to locate them.

Debian / Ubuntu users can get the necessary system packages for
RocqIDE with:

    $ sudo apt-get install libgtksourceview-3.0-dev

Opam (https://opam.ocaml.org/) is recommended to install OCaml and
the corresponding packages.

    $ opam switch create rocq --packages="ocaml-variants.4.14.1+options,ocaml-option-flambda"
    $ eval $(opam env)
    $ opam install dune ocamlfind zarith lablgtk3-sourceview3

should get you a reasonable OCaml environment to compile Rocq. See the
OPAM documentation for more help.

Nix users can also get all the required dependencies by running:

    $ nix-shell

Run-time dependencies of native compilation
-------------------------------------------

The OCaml compiler and findlib are build-time dependencies, but also
run-time dependencies if you wish to use the native compiler.

Build and install procedure
---------------------------

Note that Rocq supports a faster, but less optimized developer build,
but final users must always use the release build. See
[dev/doc/build-system.dune.md](dev/doc/build-system.dune.md)
for more details.

To build and install Rocq (and RocqIDE if desired) do:

    $ ./configure -prefix <install_prefix> $options
    $ make dunestrap
    $ dune build -p rocq-runtime,coq-core,rocq-core,coq,coqide-server,rocqide
    $ dune install --prefix=<install_prefix> rocq-runtime coq-core rocq-core coq coqide-server rocqide

You can drop the `rocqide` packages if not needed.

Packagers may want to play with `dune install` options as to tweak
installation path, the `-prefix` argument in `./configure` tells Rocq
where to find its standard library, but doesn't control any other
installation path these days.

OCaml toolchain advisory
------------------------

When loading plugins or `vo` files, you should make sure that these
were compiled with the same OCaml setup (version, flags,
dependencies...) as Rocq.  Distribution of pre-compiled plugins and
`.vo` files is only possible if users are guaranteed to have the same
Rocq version compiled with the same OCaml toolchain.  An OCaml setup
mismatch is the most probable cause for an `Error while loading ...:
implementation mismatch on ...`.

coq_environment.txt
-------------------
Rocq binaries which honor environment variables, such as `ROCQLIB`, can
be seeded values for these variables by placing a text file named
`coq_environment.txt` next to them. The file can contain assignments
like `ROCQLIB="some path"`, that is a variable name followed by `=` and
a string that follows OCaml's escaping conventions. This feature can be
used by installers of binary package to make Rocq aware of its installation
path.
