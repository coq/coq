Quick Installation Procedure using Make.
----------------------------------------

    $ ./configure
    $ make -f Makefile.make
    $ make -f Makefile.make install (you may need superuser rights)

Detailed Installation Procedure.
--------------------------------

1. Check that you have the OCaml compiler installed on your
   computer and that `ocamlc` (or, better, its native code version
   `ocamlc.opt`) is in a directory which is present in your $PATH
   environment variable. At the time of writing this document, all
   versions of Objective Caml later or equal to 4.05.0 are
   supported.

   To get Coq in native-code, (which runs 4 to 10 times faster than
   bytecode, but it takes more time to get compiled and the binary is
   bigger), you will also need the `ocamlopt` (or its native code version
   `ocamlopt.opt`) command.

2. The uncompression and un-tarring of the distribution file gave birth
   to a directory named "coq-8.xx". You can rename this directory and put
   it wherever you want. Just keep in mind that you will need some spare
   space during the compilation (reckon on about 300 Mb of disk space
   for the whole system in native-code compilation). Once installed, the
   binaries take about 30 Mb, and the library about 200 Mb.

3. First you need to configure the system. It is done automatically with
   the command:

        ./configure <options>

   The `configure` script will ask you for directories where to put
   the Coq binaries, standard library, man pages, etc. It will propose
   default values.

   For a list of options accepted by the `configure` script, run
   `./configure -help`. The main options accepted are:

   * `-prefix <dir>`
     Binaries, library, and man pages will be respectively
     installed in `<dir>/bin`, `<dir>/lib/coq`, and `<dir>/man`

   * `-bindir <dir>`                   (default: `/usr/local/bin`)
     Directory where the binaries will be installed

   * `-libdir <dir>`                   (default: `/usr/local/lib/coq`)
     Directory where the Coq standard library will be installed

   * `-mandir <dir>`                   (default: `/usr/local/share/man`)
     Directory where the Coq manual pages will be installed

   * `-arch <value>`                   (default is the result of the command `arch`)
     An arbitrary architecture name for your machine (useful when
     compiling Coq on two different architectures for which the
     result of "arch" is the same, e.g. Sun OS and Solaris)

   * `-local`
     Compile Coq to run in its source directory. The installation (step 6)
     is not necessary in that case.

   * `-browser <command>`
     Use <command> to open an URL in a browser. %s must appear in <command>,
     and will be replaced by the URL.

   * `-flambda-opts <flags>`
     This experimental option will pass specific user flags to the
     OCaml optimizing compiler. In most cases, this option is used
     to tweak the flambda backend; for maximum performance we
     recommend using:

         -flambda-opts `-O3 -unbox-closures`

     but of course you are free to try with a different combination
     of flags. You can read more at
     https://caml.inria.fr/pub/docs/manual-ocaml/flambda.html

     There is a known problem with certain OCaml versions and
     `native_compute`, that will make compilation to require
     a large amount of RAM (>= 10GiB) in some particular files.

     We recommend disabling native compilation (`-native-compiler no`)
     with flambda unless you use OCaml >= 4.07.0.

     c.f. https://caml.inria.fr/mantis/view.php?id=7630

   If you want your build to be reproducible, ensure that the
   SOURCE_DATE_EPOCH environment variable is set as documented in
   https://reproducible-builds.org/specs/source-date-epoch/

4. Still in the root directory, do

        make -f Makefile.make

   to compile Coq in the best OCaml mode available (native-code if supported,
   bytecode otherwise).

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
   defined at configuration time (step 3). Just do

        umask 022
        make -f Makefile.make install

   Of course, you may need superuser rights to do that.

6. Optionally, you could build the bytecode version of Coq via:

        make -f Makefile.make byte

   and install it via

        make -f Makefile.make install-byte

  This version is much slower than the native code version of Coq, but could
  be helpful for debugging purposes. In particular, coqtop.byte embeds an OCaml
  toplevel accessible via the Drop command.

7. You can now clean all the sources. (You can even erase them.)

        make -f Makefile.make clean

Installation Procedure For Plugin Developers.
---------------------------------------------

If you wish to write plugins you *must* keep the Coq sources, without
cleaning them. Therefore, to avoid a duplication of binaries and library,
it is not necessary to do the installation step (6- above).  You just have
to tell it at configuration step (4- above) with the option -local :

    ./configure -local <other options>

Then compile the sources as described in step 5 above. The resulting
binaries will reside in the subdirectory bin/.

Unless you pass the -nodebug option to ./configure, the -g option of the
OCaml compiler will be used during compilation to allow debugging.
See the debugging file in dev/doc and the chapter 15 of the Coq Reference
Manual for details about how to use the OCaml debugger with Coq.


The Available Commands.
-----------------------

There are two Coq commands:

    coqtop          The Coq toplevel
    coqc            The Coq compiler

Under architecture where ocamlopt is available, coqtop is the native code
version of Coq. On such architecture, you could additionally request
the build of the bytecode version of Coq via 'make byte' and install it via
'make install-byte'. This will create  an extra binary named coqtop.byte,
that could be used for debugging purpose. If native code isn't available,
coqtop.byte is directly built by 'make', and coqtop is a link to coqtop.byte.
coqc also invokes the fastest version of Coq. Options -opt and -byte to coqtop
and coqc selects a particular binary.

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

Compiling For Different Architectures.
--------------------------------------

This section explains how to compile Coq for several architecture, sharing
the same sources. The important fact is that some files are architecture
dependent (`.cmx`, `.o` and executable files for instance) but others are not
(`.cmo` and `.vo`). Consequently, you can :

-  save some time during compilation by not cleaning the architecture
   independent files;

-  save some space during installation by sharing the Coq standard
   library (which is fully architecture independent).

So, in order to compile Coq for a new architecture, proceed as follows:

* Omit step 7 above and clean only the architecture dependent files:
  it is done automatically with the command

        make -f Makefile.make archclean

* Configure the system for the new architecture:

        ./configure <options>

  You can specify the same directory for the standard library but you
  MUST specify a different directory for the binaries (of course).

* Compile and install the system as described in steps 5 and 6 above.

Moving Binaries Or Library.
---------------------------

If you move both the binaries and the library in a consistent way,
Coq should be able to still run. Otherwise, Coq may be "lost",
running "coqtop" would then return an error message of the kind:

    Error during initialization :
    Error: cannot guess a path for Coq libraries; please use -coqlib option

You can then indicate the new places to Coq, using the options -coqlib :

    coqtop -coqlib <new directory>

See also next section.

Dynamically Loaded Libraries For Bytecode Executables.
------------------------------------------------------

Some bytecode executables of Coq use the OCaml runtime, which dynamically
loads a shared library (.so or .dll). When it is not installed properly, you
can get an error message of this kind:

    Fatal error: cannot load shared library dllcoqrun
    Reason: dllcoqrun.so: cannot open shared object file: No such file or directory

In this case, you need either:

- to set the `CAML_LD_LIBRARY_PATH` environment variable to point to the
  directory where dllcoqrun.so is; this is suitable when you want to run
  the command a limited number of times in a controlled environment (e.g.
  during compilation of binary packages);
- install dllcoqrun.so in a location listed in the file ld.conf that is in
  the directory of the standard library of OCaml;
- recompile your bytecode executables after reconfiguring the location
  of the shared library:

        ./configure -vmbyteflags "-dllib,-lcoqrun,-dllpath,<path>" ...

  where `<path>` is the directory where the dllcoqrun.so is installed;
- (not recommended) compile bytecode executables with a custom OCaml
  runtime by using:

        ./configure -custom ...

  be aware that stripping executables generated this way, or performing
  other executable-specific operations, will make them useless.
