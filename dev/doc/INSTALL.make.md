Quick Installation Procedure using Make.
----------------------------------------

    $ ./configure
    $ make world
    $ make install (you may need superuser rights)

Detailed Installation Procedure.
--------------------------------

Note these installation instructions are meant for users. For Coq
developers, there is an extra set of targets better suited to them:
please see the [contributing guide](../../CONTRIBUTING.md).

1. Check that you have the required dependencies as specified in the
   top-level [INSTALL](../../INSTALL.md) file.

2. Decompress Coq's source code into a build folder; the name doesn't
   matter. You will need around 300 MiB free disk space to compile
   Coq, and a similar amount to install it.

3. Then, configure Coq with the command:

        ./configure <options>

   The `configure` script will ask you for directories where to put
   the Coq binaries, standard library, man pages, etc. It will propose
   default values.

   For a list of options accepted by the `configure` script, run
   `./configure -help`. The main options accepted are:

   * `-prefix <dir>`
     Binaries, library, and man pages will be respectively
     installed in `<dir>/bin`, `<dir>/lib/coq`, and `<dir>/man`

   * `-libdir <dir>`                   (default: `/usr/local/lib/coq`)
     Directory where the Coq standard library will be installed

   * `-mandir <dir>`                   (default: `/usr/local/share/man`)
     Directory where the Coq manual pages will be installed

   * `-arch <value>`                   (default is the result of the command `arch`)
     An arbitrary architecture name for your machine (useful when
     compiling Coq on two different architectures for which the
     result of "arch" is the same, e.g. Sun OS and Solaris)

   * `-browser <command>`
     Use <command> to open an URL in a browser. %s must appear in <command>,
     and will be replaced by the URL.

   If you want your build to be reproducible, ensure that the
   `SOURCE_DATE_EPOCH` environment variable is set as documented in
   https://reproducible-builds.org/specs/source-date-epoch/

4. Still in the Coq sources directory, do:

        make world

   to compile Coq (this builds both native and bytecode version by
   default, or only the bytecode version if a native OCaml port is not
   available).

   This will compile the entire system. This phase can take more or less time,
   depending on your architecture and is fairly verbose. On a multi-core machine,
   it is recommended to compile in parallel, via make -jN where N is your number
   of cores.

   If you wish to create timing logs for the standard library, you can
   pass `TIMING=1` (for per-line timing files) or `TIMED=1` (for
   per-file timing on stdout).  Further variables and targets are
   available for more detailed timing analysis; see the section of the
   reference manual on `coq_makefile`.  If there is any timing target
   or variable supported by `coq_makefile`-made Makefiles which is not
   supported by Coq's own Makefile, please report that as a bug.

5. You can now install the Coq system. Executables, libraries, and
   manual pages are copied in some standard places of your system,
   defined at configuration time (step 3). Just do:

        umask 022
        make install

   Of course, you may need superuser rights to do that.

6. Note that the `install` target does support the `DESTDIR` variable,
   useful for package builders, so `make DESTDIR=tmp install` will
   install the files under `tmp/usr/...`.

7. You can now clean all the sources. (You can even erase them.)

        make clean

Notes for packagers
-------------------

The `make install` target for Coq's OCaml parts calls `dune install`
internally. Before Dune 2.9, `dune install` didn't support configuring
the `-docdir` and `-configdir` installation paths, thus these
configure options were ignored for the `coq-core` package.

Coq will try to detect if Dune >= 2.9 is being used, and perform the
right call to Dune in that case. If Dune < 2.9 is being used, Coq's
configure will emit a warning. As a packager/user, you have two
options: a) manually correct the install locations of `doc` and `etc`
for `coq-core`, or to use a tool such as `opam-install` which already
supports these options correctly. `dune build -p coq-core &&
opam-installer $OPTS _build/default/coq-core.install` should do the
trick.

Installation Procedure For Plugin Developers.
---------------------------------------------

If you wish to write plugins you *must* keep the Coq sources, without
cleaning them. Therefore, to avoid a duplication of binaries and library,
it is not necessary to do the installation step (6- above).  You just have
to tell it at configuration step (4- above) with the option -local :

    ./configure -profile devel <other options>

Then compile the sources as described in step 5 above. The resulting
binaries will reside in the subdirectory `bin`, which is symlink to
the `_build_vo/default/bin` directory.

Unless you pass the `-nodebug` option to `./configure`, the `-g`
option of the OCaml compiler will be used during compilation to allow
debugging.  See the debugging file in `dev/doc` and the chapter 15 of
the Coq Reference Manual for details about how to use the OCaml
debugger with Coq.


The Available Commands.
-----------------------

There are two Coq commands:

    coqtop          The Coq toplevel
    coqc            The Coq compiler

For architectures where `ocamlopt` is available, `coqtop` is the
native code version of Coq. The byte-code version is `coqtop.byte`,
which can be used for debugging. If native code isn't available,
`coqtop` will point to `coqtop.byte`. `coqc` follows a similar scheme.

* `coqtop` launches Coq in the interactive mode. By default it loads
  basic logical definitions and tactics from the Init directory.

* `coqc` allows compilation of Coq files directly from the command line.
  To compile a file foo.v, do:

        coqc foo.v

  It will produce a file `foo.vo`, that you can now load through the Coq
  command `Require`.

  A detailed description of these commands and of their options is given
  in the Reference Manual (which you can get in the doc/
  directory, or read online on http://coq.inria.fr/doc/)
  and in the corresponding manual pages.

Moving Binaries Or Library.
---------------------------

If you move both the binaries and the library in a consistent way, Coq
should still be able to run. Otherwise, Coq may not be able to find
the required prelude files and will give this error message:

    Error during initialization :
    Error: cannot guess a path for Coq libraries; please use -coqlib option

You can then indicate the location of the Coq's standard library using
the option `-coqlib`:

    coqtop -coqlib <new directory>

# FLambda Options

You can tweak the optimization flags passed to the OCaml optimizing
compiler. Coq's default is:

    -flambda-opts `-O3 -unbox-closures`

which is set in Coq's toplevel `dune` file. Feel free to try a
different combination of flags. You can read more at
https://caml.inria.fr/pub/docs/manual-ocaml/flambda.html

There is a known problem with certain OCaml versions and
`native_compute`, that will make compilation require a large amount of
RAM (>= 10GiB) for some particular files.

Dynamically Loaded Libraries For Bytecode Executables.
------------------------------------------------------

Some bytecode executables of Coq use the OCaml runtime, which
dynamically loads a shared library (`.so` or `.dll`). When it is not
installed properly, you can get an error message of this kind:

    Fatal error: cannot load shared library dllcoqrun
    Reason: dllcoqrun.so: cannot open shared object file: No such file or directory

In this case, you need either:

- to set the `CAML_LD_LIBRARY_PATH` environment variable to point to the
  directory where dllcoqrun.so is; this is suitable when you want to run
  the command a limited number of times in a controlled environment (e.g.
  during compilation of binary packages);

- install `dllcoqrun.so` in a location listed in the file `ld.conf` that is in
  the directory of the standard library of OCaml
