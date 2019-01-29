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

let print_usage_common co command =
  output_string co command;
  output_string co "Coq options are:\n";
  output_string co
"  -I dir                 look for ML files in dir\
\n  -include dir           (idem)\
\n  -R dir coqdir          recursively map physical dir to logical coqdir\
\n  -Q dir coqdir          map physical dir to logical coqdir\
\n  -top coqdir            set the toplevel name to be coqdir instead of Top\
\n  -topfile f             set the toplevel name as though compiling f\
\n  -coqlib dir            set the coq standard library directory\
\n  -exclude-dir f         exclude subdirectories named f for option -R\
\n\
\n  -noinit                start without loading the Init library\
\n  -nois                  (idem)\
\n  -compat X.Y            provides compatibility support for Coq version X.Y\
\n\
\n  -load-ml-object f      load ML object file f\
\n  -load-ml-source f      load ML file f\
\n  -load-vernac-source f  load Coq file f.v (Load \"f\".)\
\n  -l f                   (idem)\
\n  -require path          load Coq library path and import it (Require Import path.)\
\n  -load-vernac-source-verbose f  load Coq file f.v (Load Verbose \"f\".)\
\n  -lv f	           (idem)\
\n  -load-vernac-object path  load Coq library path (Require path)\
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
\n  -emacs                 tells Coq it is executed under Emacs\
\n\
\n  -q                     skip loading of rcfile\
\n  -init-file f           set the rcfile to f\
\n  -bt                    print backtraces (requires configure debug flag)\
\n  -debug                 debug mode (implies -bt)\
\n  -diffs (on|off|removed) highlight differences between proof steps\
\n  -stm-debug             STM debug mode (will trace every transaction)\
\n  -noglob                do not dump globalizations\
\n  -dump-glob f           dump globalizations in file f (to be used by coqdoc)\
\n  -impredicative-set     set sort Set impredicative\
\n  -allow-sprop           allow using the proof irrelevant SProp sort\
\n  -sprop-cumulative      make sort SProp cumulative with the rest of the hierarchy\
\n  -indices-matter        levels of indices (and nonuniform parameters) contribute to the level of inductives\
\n  -type-in-type          disable universe consistency checking\
\n  -no-template-check     disable checking of universes constraints on universes parameterizing template polymorphic inductive types\
\n  -mangle-names x        mangle auto-generated names using prefix x\
\n  -set \"Foo Bar\"         enable Foo Bar (as Set Foo Bar. in a file)\
\n  -set \"Foo Bar=value\"   set Foo Bar to value (value is interpreted according to Foo Bar's type)\
\n  -unset \"Foo Bar\"       disable Foo Bar (as Unset Foo Bar. in a file)\
\n  -time                  display the time taken by each command\
\n  -profile-ltac          display the time taken by each (sub)tactic\
\n  -m, --memory           display total heap size at program exit\
\n                         (use environment variable\
\n                          OCAML_GC_STATS=\"/tmp/gclog.txt\"\
\n                          for full Gc stats dump)\
\n  -bytecode-compiler (yes|no)        enable the vm_compute reduction machine\
\n  -native-compiler (yes|no|ondemand) enable the native_compute reduction machine\
\n  -h, -help, --help      print this list of options\
\n";
  List.iter (fun (name, text) ->
    output_string co
     ("\nWith the flag '-toploop "^name^
        "' these extra option are also available:\n"^
      text^"\n"))
    !extra_usage

(* print the usage on standard error *)

let print_usage_coqtop () =
  print_usage_common stderr "Usage: coqtop <options>\n\n";
  output_string stderr "\n\
coqtop specific options:\
\n\
\n  -batch                 batch mode (exits just after argument parsing)\
\n\
\nDeprecated options [use coqc instead]:\
\n\
\n  -compile f.v           compile Coq file f.v (implies -batch)\
\n  -compile-verbose f.v   verbosely compile Coq file f.v (implies -batch)\
\n  -o f.vo                use f.vo as the output file name\
\n";
  flush stderr ;
  exit 1

let print_usage_coqc () =
  print_usage_common stderr "Usage: coqc <options> <Coq options> file...\n\n";
  output_string stderr "\n\
coqc specific options:\
\n\
\n  -o f.vo                use f.vo as the output file name\
\n  -verbose               compile and output the input file\
\n  -quick                 quickly compile .v files to .vio files (skip proofs)\
\n  -schedule-vio2vo j f1..fn   run up to j instances of Coq to turn each fi.vio\
\n                         into fi.vo\
\n  -schedule-vio-checking j f1..fn   run up to j instances of Coq to check all\
\n                         proofs in each fi.vio\
\n\
\nUndocumented:\
\n  -vio2vo                [see manual]\
\n  -check-vio-tasks       [see manual]\
\n\
\nDeprecated options:\
\n\
\n  -image f               specify an alternative executable for Coq\
\n  -opt                   run the native-code version of Coq\
\n  -byte                  run the bytecode version of Coq\
\n  -t                     keep temporary files\
\n  -outputstate file      save summary state in file \
\n";
  flush stderr ;
  exit 1
