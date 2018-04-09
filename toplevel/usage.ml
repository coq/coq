(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let version ret =
  Printf.printf "The Coq Proof Assistant, version %s (%s)\n"
    Coq_config.version Coq_config.date;
  Printf.printf "compiled on %s with OCaml %s\n" Coq_config.compile_date Coq_config.caml_version;
  exit ret
let machine_readable_version ret =
  Printf.printf "%s %s\n"
    Coq_config.version Coq_config.caml_version;
  exit ret

(* print the usage of coqtop (or coqc) on channel co *)

let extra_usage = ref []
let add_to_usage name text = extra_usage := (name,text) :: !extra_usage

let print_usage_channel co command =
  output_string co command;
  output_string co "Coq options are:\n";
  output_string co
"  -I dir                 look for ML files in dir\
\n  -include dir           (idem)\
\n  -R dir coqdir          recursively map physical dir to logical coqdir\
\n  -Q dir coqdir          map physical dir to logical coqdir\
\n  -top coqdir            set the toplevel name to be coqdir instead of Top\
\n  -coqlib dir            set the coq standard library directory\
\n  -exclude-dir f         exclude subdirectories named f for option -R\
\n\
\n  -noinit                start without loading the Init library\
\n  -nois                  (idem)\
\n  -compat X.Y            provides compatibility support for Coq version X.Y\
\n\
\n  -load-ml-object f      load ML object file f\
\n  -load-ml-source f      load ML file f\
\n  -load-vernac-source f  load Coq file f.v (Load f.)\
\n  -l f                   (idem)\
\n  -load-vernac-source-verbose f  load Coq file f.v (Load Verbose f.)\
\n  -lv f	                 (idem)\
\n  -load-vernac-object f  load Coq object file f.vo\
\n  -require path          load Coq library path and import it (Require Import path.)\
\n  -compile f.v           compile Coq file f.v (implies -batch)\
\n  -compile-verbose f.v   verbosely compile Coq file f.v (implies -batch)\
\n  -o f.vo                use f.vo as the output file name\
\n  -quick                 quickly compile .v files to .vio files (skip proofs)\
\n  -schedule-vio2vo j f1..fn   run up to j instances of Coq to turn each fi.vio\
\n                         into fi.vo\
\n  -schedule-vio-checking j f1..fn   run up to j instances of Coq to check all\
\n                         proofs in each fi.vio\
\n\
\n  -where                 print Coq's standard library location and exit\
\n  -config, --config      print Coq's configuration information and exit\
\n  -v, --version          print Coq version and exit\
\n  -print-version         print Coq version in easy to parse format and exit\
\n  -list-tags             print highlight color tags known by Coq and exit\
\n\
\n  -quiet                 unset display of extra information (implies -w \"-all\")\
\n  -w (w1,..,wn)          configure display of warnings\
\n  -color (yes|no|auto)   configure color output\
\n\
\n  -q                     skip loading of rcfile\
\n  -init-file f           set the rcfile to f\
\n  -batch                 batch mode (exits just after arguments parsing)\
\n  -boot                  boot mode (implies -q and -batch)\
\n  -bt                    print backtraces (requires configure debug flag)\
\n  -debug                 debug mode (implies -bt)\
\n  -diffs (on|off|removed) highlight differences between proof steps\
\n  -stm-debug             STM debug mode (will trace every transaction)\
\n  -emacs                 tells Coq it is executed under Emacs\
\n  -noglob                do not dump globalizations\
\n  -dump-glob f           dump globalizations in file f (to be used by coqdoc)\
\n  -impredicative-set     set sort Set impredicative\
\n  -indices-matter        levels of indices (and nonuniform parameters) contribute to the level of inductives\
\n  -type-in-type          disable universe consistency checking\
\n  -mangle-names x        mangle auto-generated names using prefix x\
\n  -time                  display the time taken by each command\
\n  -profile-ltac          display the time taken by each (sub)tactic\
\n  -m, --memory           display total heap size at program exit\
\n                         (use environment variable\
\n                          OCAML_GC_STATS=\"/tmp/gclog.txt\"\
\n                          for full Gc stats dump)\
\n  -native-compiler       precompile files for the native_compute machinery\
\n  -h, -help, --help      print this list of options\
\n";
  List.iter (fun (name, text) ->
    output_string co
     ("\nWith the flag '-toploop "^name^
        "' these extra option are also available:\n"^
      text^"\n"))
    !extra_usage

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_coqtop () =
  print_usage "Usage: coqtop <options>\n\n";
  flush stderr ;
  exit 1

let print_usage_coqc () =
  print_usage "Usage: coqc <options> <Coq options> file...\n\
\noptions are:\
\n  -verbose  compile verbosely\
\n  -image f  specify an alternative executable for Coq\
\n  -opt      run the native-code version of Coq\
\n  -byte     run the bytecode version of Coq\
\n  -t        keep temporary files\n\n";
  flush stderr ;
  exit 1

