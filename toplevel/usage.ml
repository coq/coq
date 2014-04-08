(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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
"  -I dir                 look for ML files in dir\
\n  -include dir           (idem)\
\n  -I dir -as coqdir      implicitly map physical dir to logical coqdir\
\n  -R dir -as coqdir      recursively map physical dir to logical coqdir\
\n  -R dir coqdir          (idem)\
\n  -Q dir coqdir          map physical dir to logical coqdir\
\n  -top coqdir            set the toplevel name to be coqdir instead of Top\
\n  -notop                 set the toplevel name to be the empty logical path\
\n  -exclude-dir f         exclude subdirectories named f for option -R\
\n\
\n  -noinit                start without loading the Init library\
\n  -nois                  (idem)\
\n  -inputstate f          read state from file f.coq\
\n  -is f                  (idem)\
\n  -outputstate f         write state in file f.coq\
\n  -compat X.Y            provides compatibility support for Coq version X.Y\
\n  -verbose-compat-notations  be warned when using compatibility notations\
\n  -no-compat-notations   get an error when using compatibility notations\
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
\n  -batch                 batch mode (exits just after arguments parsing)\
\n  -boot                  boot mode (implies -q and -batch)\
\n  -bt                    print backtraces (requires configure debug flag)\
\n  -debug                 debug mode (implies -bt)\
\n  -emacs                 tells Coq it is executed under Emacs\
\n  -noglob                do not dump globalizations\
\n  -dump-glob f           dump globalizations in file f (to be used by coqdoc)\
\n  -with-geoproof (yes|no) to (de)activate special functions for Geoproof within Coqide (default is yes)\
\n  -impredicative-set     set sort Set impredicative\

\n  -force-load-proofs     load opaque proofs in memory initially\
\n  -lazy-load-proofs      load opaque proofs in memory by necessity (default)\
\n  -dont-load-proofs      see opaque proofs as axioms instead of loading them\
\n  -xml                   export XML files either to the hierarchy rooted in\
\n                         the directory $COQ_XML_LIBRARY_ROOT (if set) or to\
\n                         stdout (if unset)\
\n  -quality               improve the legibility of the proof terms produced by\
\n                         some tactics\
\n  -time                  display the time taken by each command\
\n  -h, --help             print this list of options\
\n  --help-XML-protocol    print the documentation of the XML protocol used by CoqIDE\
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
  Printf.printf "COQLIB=%s/\n" (Envars.coqlib ());
  Printf.printf "DOCDIR=%s/\n" (Envars.docdir ());
  Printf.printf "OCAMLDEP=%s\n" Coq_config.ocamldep;
  Printf.printf "OCAMLC=%s\n" Coq_config.ocamlc;
  Printf.printf "OCAMLOPT=%s\n" Coq_config.ocamlopt;
  Printf.printf "OCAMLDOC=%s\n" Coq_config.ocamldoc;
  Printf.printf "CAMLBIN=%s/\n" (Envars.camlbin ());
  Printf.printf "CAMLLIB=%s/\n" (Envars.camllib ());
  Printf.printf "CAMLP4=%s\n" Coq_config.camlp4;
  Printf.printf "CAMLP4O=%s\n" Coq_config.camlp4o;
  Printf.printf "CAMLP4BIN=%s/\n" (Envars.camlp4bin ());
  Printf.printf "CAMLP4LIB=%s\n" (Envars.camlp4lib ());
  Printf.printf "CAMLP4OPTIONS=%s\n" Coq_config.camlp4compat;
  Printf.printf "HASNATDYNLINK=%s\n" (if Coq_config.has_natdynlink then "true" else "false")
