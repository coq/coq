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
  output_string co "Options are:\n";
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
  -load-vernac-object f  load Coq object file f.vo
  -require f             load Coq object file f.vo and import it (Require f.)

  -opt                   run the native-code version of Coq or Coq_SearchIsos
  -image f               specify an alternative binary image f
  -bindir dir            specify an alternative directory for the binaries
  -libdir dir            specify an alternative directory for the library

  -where                 print Coq's standard library location and exit
  -v                     print Coq version and exit

  -q                     skip loading of rcfile
  -init-file f           set the rcfile to f
  -user u                use the rcfile of user u
  -batch                 batch mode (exits just after arguments parsing)
  -emacs                 tells Coq it is executed under Emacs
"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_coqtop () =
  print_usage "Usage: coqtop <options>\n";
  output_string stderr
"  -searchisos            run Coq_SearchIsos\n"

let print_usage_coqc () =
  print_usage "Usage: coqc [-i] [-t] <options> file...\n
  -i  compile specification only (in file.vi)
  -t  keep temporary files\n\n"
