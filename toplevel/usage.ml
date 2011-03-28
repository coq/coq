(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let version ret =
  Printf.printf "The Coq Proof Assistant, version %s (%s)\n"
    Coq_config.version Coq_config.date;
  Printf.printf "compiled on %s with OCaml %s\n" Coq_config.compile_date Coq_config.caml_version;
  exit ret

(* print the usage of coqtop (or coqc) on channel co *)

let print_usage_channel co command =
  output_string co command;
  output_string co "Coq options are:\n";
  output_string co
"  -I dir -as coqdir      map physical dir to logical coqdir\
\n  -I dir                 map directory dir to the empty logical path\
\n  -include dir           (idem)\
\n  -R dir -as coqdir      recursively map physical dir to logical coqdir\
\n  -R dir coqdir          (idem)\
\n  -top coqdir            set the toplevel name to be coqdir instead of Top\
\n  -notop                 set the toplevel name to be the empty logical path\
\n  -exclude-dir f         exclude subdirectories named f for option -R\
\n\
\n  -inputstate f          read state from file f.coq\
\n  -is f                  (idem)\
\n  -nois                  start with an empty state\
\n  -outputstate f         write state in file f.coq\
\n  -compat X.Y            provides compatibility support for Coq version X.Y\
\n\
\n  -load-ml-object f      load ML object file f\
\n  -load-ml-source f      load ML file f\
\n  -load-vernac-source f  load Coq file f.v (Load f.)\
\n  -l f                   (idem)\
\n  -load-vernac-source-verbose f  load Coq file f.v (Load Verbose f.)\
\n  -lv f	                 (idem)\
\n  -load-vernac-object f  load Coq object file f.vo\
\n  -require f             load Coq object file f.vo and import it (Require f.)\
\n  -compile f             compile Coq file f.v (implies -batch)\
\n  -compile-verbose f     verbosely compile Coq file f.v (implies -batch)\
\n\
\n  -opt                   run the native-code version of Coq\
\n  -byte                  run the bytecode version of Coq\
\n\
\n  -where                 print Coq's standard library location and exit\
\n  -config                print Coq's configuration information and exit\
\n  -v                     print Coq version and exit\
\n\
\n  -q                     skip loading of rcfile\
\n  -init-file f           set the rcfile to f\
\n  -user u                use the rcfile of user u\
\n  -batch                 batch mode (exits just after arguments parsing)\
\n  -boot                  boot mode (implies -q and -batch)\
\n  -emacs                 tells Coq it is executed under Emacs\
\n  -noglob                do not dump globalizations\
\n  -dump-glob f           dump globalizations in file f (to be used by coqdoc)\
\n  -with-geoproof (yes|no) to (de)activate special functions for Geoproof within Coqide (default is yes)\
\n  -impredicative-set     set sort Set impredicative\
\n  -load-proofs           load opaque proofs in memory (default)\
\n  -dont-load-proofs      don't load opaque proofs in memory\
\n  -xml                   export XML files either to the hierarchy rooted in\
\n                         the directory $COQ_XML_LIBRARY_ROOT (if set) or to\
\n                         stdout (if unset)\
\n  -quality               improve the legibility of the proof terms produced by\
\n                         some tactics\
\n  -h, --help             print this list of options\
\n"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_coqtop () =
  print_usage "Usage: coqtop <options>\n\n"

let print_usage_coqc () =
  print_usage "Usage: coqc <options> <Coq options> file...\n\
\noptions are:\
\n  -verbose  compile verbosely\
\n  -image f  specify an alternative executable for Coq\
\n  -t        keep temporary files\n\n"

(* Print the configuration information *)

let print_config () =
  if Coq_config.local then Printf.printf "LOCAL=1\n" else Printf.printf "LOCAL=0\n";
  Printf.printf "COQLIB=%s/\n" Coq_config.coqlib;
  Printf.printf "COQSRC=%s/\n" Coq_config.coqsrc;
  Printf.printf "CAMLBIN=%s/\n" Coq_config.camlbin;
  Printf.printf "CAMLLIB=%s/\n" Coq_config.camllib;
  Printf.printf "CAMLP4=%s\n" Coq_config.camlp4;
  Printf.printf "CAMLP4BIN=%s\n" Coq_config.camlp4bin;
  Printf.printf "CAMLP4LIB=%s\n" Coq_config.camlp4lib


