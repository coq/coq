(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

let version () =
  Printf.printf "The Coq Proof Assistant, version %s (%s)\n"
    Coq_config.version Coq_config.date;
  Printf.printf "compiled on %s\n" Coq_config.compile_date;
  exit 0

(* print the usage of coqtop (or coqc) on channel co *)

let print_usage_channel co command =
  output_string co command;
  output_string co "Coq options are:\n";
  output_string co
"  -I dir                 add directory dir in the include path
  -include dir           (idem)
  -R dir coqdir          recursively map physical dir to logical coqdir 
  -src                   add source directories in the include path

  -inputstate f          read state from file f.coq
  -is f                  (idem)
  -nois                  start with an empty state
  -outputstate f         write state in file f.coq

  -load-ml-object f      load ML object file f 
  -load-ml-source f      load ML file f 
  -load-vernac-source f  load Coq file f.v (Load f.)
  -l f                   (idem) 
  -load-vernac-object f  load Coq object file f.vo
  -require f             load Coq object file f.vo and import it (Require f.)
  -compile f             compile Coq file f.v (implies -batch)
  -compile-verbose f     verbosely compile Coq file f.v (implies -batch)

  -opt                   run the native-code version of Coq or Coq_SearchIsos
  -byte                  run the bytecode version of Coq or Coq_SearchIsos

  -where                 print Coq's standard library location and exit
  -v                     print Coq version and exit

  -q                     skip loading of rcfile
  -init-file f           set the rcfile to f
  -user u                use the rcfile of user u
  -batch                 batch mode (exits just after arguments parsing)
  -boot                  boot mode (implies -q and -batch)
  -emacs                 tells Coq it is executed under Emacs
  -dump-glob f           dump globalizations in file f (to be used by coqdoc)
  -xml                   exports XML files either to the hierarchy rooted in
                         the directory $COQ_XML_LIBRARY_ROOT (if set) or to
                         stdout (if unset)
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
