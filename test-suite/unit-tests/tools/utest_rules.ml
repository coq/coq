open Format

let subdirs =
  [ "lib", "coq-core.lib"
  ; "clib", "coq-core.clib"
  (* linking only coq-core.printing is *not* enough! .mlg have to be loaded so
     coq-core.toplevel is a better option. *)
  ; "printing", "coq-core.toplevel"
  ]

let filter_ext ~ext files =
  List.filter (fun file -> Filename.check_suffix file ext) files

let replace_ext ~ext file =
  Filename.remove_extension file ^ ext

let gen_prelude ~libraries fmt files =
  let exes = List.map Filename.remove_extension files in
  fprintf fmt
    "(executables@\n (names %a)@\n (libraries coq_utest %s))"
    (pp_print_list pp_print_string) exes libraries

let output_log_rule fmt file =
  let exe = replace_ext ~ext:".exe" file in
  fprintf fmt
    "(rule@\n (targets %s.log)@\n (action (with-accepted-exit-codes 0 (run ./%s))))"
    file exe

let gen_postlude fmt () =
  fprintf fmt "(alias@\n (name runtest) (deps (glob_files *.ml.log)))"

let gen_for_subdir fmt (dir, libraries) =
  let files = Array.to_list (Sys.readdir dir) in
  let files = filter_ext ~ext:".ml" files in
  fprintf fmt "(subdir %s@\n @[%a@\n@\n@[<v>%a@]@\n@\n%a@])@\n@\n"
    dir
    (gen_prelude ~libraries) files
    (pp_print_list output_log_rule) files
    gen_postlude ()

let _ =
  let out = open_out "../../utest_dune" in
  let fmt = formatter_of_out_channel out in
  List.iter (gen_for_subdir fmt) subdirs;
  pp_print_flush fmt ();
  close_out out
