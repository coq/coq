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


Debugging with ocamldebug from Emacs or command line
====================================================

See [build-system.dune.md#ocamldebug](build-system.dune.md#ocamldebug)

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
