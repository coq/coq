(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let version () =
  Printf.printf "The Coq Proof Assistant, version %s\n" Coq_config.version;
  Printf.printf "compiled with OCaml %s\n" Coq_config.caml_version

let machine_readable_version () =
  Printf.printf "%s %s\n"
    Coq_config.version Coq_config.caml_version

(* print the usage of coqtop (or coqc) on channel co *)

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
\n  -boot                  don't bind the `Coq.` prefix to the default -coqlib dir\
\n  -noinit                don't load Coq.Init.Prelude on start \
\n  -nois                  (idem)\
\n  -compat X.Y            provides compatibility support for Coq version X.Y\
\n\
\n  -load-vernac-source f  load Coq file f.v (Load \"f\".)\
\n  -l f                   (idem)\
\n  -load-vernac-source-verbose f  load Coq file f.v (Load Verbose \"f\".)\
\n  -lv f	           (idem)\
\n  -load-vernac-object lib\
\n                         load Coq library lib (Require lib)\
\n  -rfrom root lib        load Coq library lib (From root Require lib.)\
\n  -require-import lib, -ri lib\
\n                         load and import Coq library lib\
\n                         (equivalent to Require Import lib.)\
\n  -require-export lib, -re lib\
\n                         load and transitively import Coq library lib\
\n                         (equivalent to Require Export lib.)\
\n  -require-import-from root lib, -rifrom root lib\
\n                         load and import Coq library lib\
\n                         (equivalent to From root Require Import lib.)\
\n  -require-export-from root lib, -refrom root lib\
\n                         load and transitively import Coq library lib\
\n                         (equivalent to From root Require Export lib.)\
\n\
\n  -where                 print Coq's standard library location and exit\
\n  -config, --config      print Coq's configuration information and exit\
\n  -v, --version          print Coq version and exit\
\n  -print-version         print Coq version in easy to parse format and exit\
\n  -list-tags             print highlight color tags known by Coq and exit\
\n\
\n  -quiet                 unset display of extra information (implies -w \"-all\")\
\n  -w (w1,..,wn)          configure display of warnings\
\n  -d (d1,..,dn)          configure display of debug messages\
\n                         some common values are:\
\n                           all         print all debugging information\
\n                           backtrace   same as -bt\
\n                         use the vernac command \"Test Debug\" to see all\
\n\
\n  -color (yes|no|auto)   configure color output\
\n  -emacs                 tells Coq it is executed under Emacs\
\n\
\n  -q                     skip loading of rcfile\
\n  -init-file f           set the rcfile to f\
\n  -bt                    print OCaml backtraces\
\n  -diffs (on|off|removed) highlight differences between proof steps\
\n  -impredicative-set     set sort Set impredicative\
\n  -allow-sprop           allow using the proof irrelevant SProp sort\
\n  -disallow-sprop        forbid using the proof irrelevant SProp sort\
\n  -indices-matter        levels of indices (and nonuniform parameters) contribute to the level of inductives\
\n  -type-in-type          disable universe consistency checking\
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
\n  -native-output-dir     <directory> set the output directory for native objects\
\n  -nI dir                OCaml include directories for the native compiler (default if not set) \
\n  -h, -help, --help      print this list of options\
\n"

(* print the usage *)

type specific_usage = {
  executable_name : string;
  extra_args : string;
  extra_options : string;
}

let print_usage co { executable_name; extra_args; extra_options } =
  print_usage_common co ("Usage: " ^ executable_name ^ " <options> " ^ extra_args ^ "\n\n");
  output_string co extra_options
