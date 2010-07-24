(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let version () =
  Printf.printf "The Coq Proof Assistant, version %s (%s)\n"
    Coq_config.version Coq_config.date;
  Printf.printf "compiled on %s with OCaml %s\n" Coq_config.compile_date Coq_config.caml_version;
  exit 0

(* print the usage of coqtop (or coqc) on channel co *)

let print_usage_channel co command =
  output_string co command;
  output_string co "Coq options are:\n";
  output_string co
"  -I dir -as coqdir      map physical dir to logical coqdir
  -I dir                 map directory dir to the empty logical path
  -include dir           (idem)
  -R dir -as coqdir      recursively map physical dir to logical coqdir
  -R dir coqdir          (idem)
  -top coqdir            set the toplevel name to be coqdir instead of Top
  -notop    r            set the toplevel name to be the empty logical path
  -exclude-dir f         exclude subdirectories named f for option -R

  -inputstate f          read state from file f.coq
  -is f                  (idem)
  -nois                  start with an empty state
  -outputstate f         write state in file f.coq
  -compat X.Y            provides compatibility support for Coq version X.Y

  -load-ml-object f      load ML object file f
  -load-ml-source f      load ML file f
  -load-vernac-source f  load Coq file f.v (Load f.)
  -l f                   (idem)
  -load-vernac-source-verbose f  load Coq file f.v (Load Verbose f.)
  -lv f	                 (idem)
  -load-vernac-object f  load Coq object file f.vo
  -require f             load Coq object file f.vo and import it (Require f.)
  -compile f             compile Coq file f.v (implies -batch)
  -compile-verbose f     verbosely compile Coq file f.v (implies -batch)

  -opt                   run the native-code version of Coq
  -byte                  run the bytecode version of Coq

  -where                 print Coq's standard library location and exit
  -config                print Coq's configuration information and exit
  -v                     print Coq version and exit

  -q                     skip loading of rcfile
  -init-file f           set the rcfile to f
  -user u                use the rcfile of user u
  -batch                 batch mode (exits just after arguments parsing)
  -boot                  boot mode (implies -q and -batch)
  -emacs                 tells Coq it is executed under Emacs
  -noglob                do not dump globalizations
  -dump-glob f           dump globalizations in file f (to be used by coqdoc)
  -with-geoproof (yes|no) to (de)activate special functions for Geoproof within Coqide (default is yes)
  -impredicative-set     set sort Set impredicative
  -dont-load-proofs      don't load opaque proofs in memory
  -xml                   export XML files either to the hierarchy rooted in
                         the directory $COQ_XML_LIBRARY_ROOT (if set) or to
                         stdout (if unset)
  -quality               improve the legibility of the proof terms produced by
                         some tactics
  -h, --help             print this list of options
"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_coqtop () =
  print_usage "Usage: coqtop <options>\n\n"

let print_usage_coqc () =
  print_usage "Usage: coqc <options> <Coq options> file...\n
options are:
  -verbose  compile verbosely
  -image f  specify an alternative executable for Coq
  -t        keep temporary files\n\n"

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


