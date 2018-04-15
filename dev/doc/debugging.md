Debugging from Coq toplevel using Caml trace mechanism
======================================================

  1. Launch bytecode version of Coq (coqtop.byte)
  2. Access Ocaml toplevel using vernacular command 'Drop.'
  3. Install load paths and pretty printers for terms, idents, ... using
     Ocaml command '#use "base_include";;' (use '#use "include";;' for 
     installing the advanced term pretty printers)
  4. Use #trace to tell which function(s) to trace
  5. Go back to Coq toplevel with 'go();;'
  6. Test your Coq command and observe the result of tracing your functions
  7. Freely switch from Coq to Ocaml toplevels with 'Drop.' and 'go();;'

  You can avoid typing #use "include" (or "base_include") after Drop
  by adding the following lines in your $HOME/.ocamlinit :

   if Filename.basename Sys.argv.(0) = "coqtop.byte"
   then ignore (Toploop.use_silently Format.std_formatter "include")

  Hints: To remove high-level pretty-printing features (coercions,
  notations, ...), use "Set Printing All". It will affect the #trace
  printers too.


Debugging with ocamldebug from Emacs
====================================

   Requires [Tuareg mode](https://github.com/ocaml/tuareg) in Emacs.\
   Coq must be configured with `-local` (`./configure -local`) and the
   byte-code version of `coqtop` must have been generated with `make byte`.

   1. M-x camldebug
   2. give the binary name bin/coqtop.byte
   3. give ../dev/ocamldebug-coq
   4. source db  (to get pretty-printers)
   5. add breakpoints with C-x C-a C-b from the buffer displaying the ocaml
      source
   6. get more help from ocamldebug manual
         run
	 step
         back
         start
	 next
	 last
	 print x (abbreviated into p x)
	 ...
   7. some hints: 

   - To debug a failure/error/anomaly, add a breakpoint in
     `Vernac.interp_vernac` (in `toplevel/vernac.ml`) at the with clause of the "try ... interp com
     with ..." block, then go "back" a few steps to find where the
     failure/error/anomaly has been raised
   - Alternatively, for an error or an anomaly, add breakpoints in the middle  
     of each of error* functions or anomaly* functions in lib/util.ml
   - If "source db" fails, do a "make printers" and try again (it should build
     top_printers.cmo and the core cma files).
   - If you build Coq with an OCaml version earlier than 4.06, and have the 
     OCAMLRUNPARAM environment variable set, Coq may hang on startup when run 
     from the debugger. If this happens, unset the variable, re-start Emacs, and 
     run the debugger again.

Debugging with ocamldebug from the command line
===============================================

In the `coq` directory:
1. (on Cygwin/Windows) Pass the `-no-custom` option to the `configure` script before building Coq.
2. Run `make` (to compile the .v files)
3. Run `make byte`
4. (on Cygwin/Windows) Add the full pathname of the directory `.../kernel/byterun` to your bash PATH.
   Alternatively, copy the file `kernel/byterun/dllcoqrun.dll` to a directory that is in the PATH.  (The
   CAML_LD_LIBRARY_PATH mechanism described at the end of INSTALL isn't working.)
5. Run `dev/ocamldebug-coq bin/coqtop.byte`  (on Cygwin/Windows, use `... bin/coqtop.byte.exe`)
6. Enter `source db` to load printers
7. Enter `set arguments -coqlib .` so Coq can find plugins, theories, etc.
8. See the ocamldebug manual for more information.  A few points:
   - use `break @ Printer 501` to set a breakpoint on line 501 in the Printer module (printer.ml).
     `break` can be abbreviated as `b`.
   - `backtrace` or `bt` to see the call stack
   - `step` or `s` goes into called functions; `next` or `n` skips over them
   - `list` or `li` shows the code just before and after the current stack frame
   - `print <var>` or `p <var>` to see the value of a variable
Note that `make byte` doesn't recompile .v files.  `make` recompiles all of them if there
are changes in any .ml file--safer but much slower.

Global gprof-based profiling
============================

   Coq must be configured with option -profile

   1. Run native Coq which must end normally (use Quit or option -batch)
   2. gprof ./coqtop gmon.out

Per function profiling
======================

   To profile function foo in file bar.ml, add the following lines, just
   after the definition of the function:

     let fookey = CProfile.declare_profile "foo";;
     let foo a b c = CProfile.profile3 fookey foo a b c;;

   where foo is assumed to have three arguments (adapt using
   Profile.profile1, Profile. profile2, etc).

   This has the effect to cumulate the time passed in foo under a
   line of name "foo" which is displayed at the time coqtop exits.
