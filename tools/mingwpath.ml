(** Mingwpath *)

(** Converts mingw-encoded filenames such as:

      /c/Program Files/Ocaml/bin

    to a more windows-friendly form (but still with / instead of \) :

      c:/Program Files/Ocaml/bin

    This nice hack was suggested by Benjamin Monate (cf bug #2526)
    to mimic the cygwin-specific tool cygpath
*)

print_string Sys.argv.(1)
