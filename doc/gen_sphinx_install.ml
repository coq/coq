open Format
let out = std_formatter
let pp_string fmt s = fprintf fmt "%s@\n" s
let pp_array pp fmt a = Array.iter (fun f -> fprintf fmt "@[%a@]@\n" pp f) a

let gen_install files =
  let pp_file fmt file = fprintf fmt "(%s as refman/%s)" file file in
  fprintf out "(install (section doc) (package coq-refman)@\n (files @[%a@]))" (pp_array pp_file) files

let list_files path =
  try Sys.readdir path with _ -> [||]

(* let gen_files files =
 *   fprintf out "@[%a@]" (pp_array pp_string) files *)

let () =
  let files = list_files "sphinx_build/html" in
  (* gen_files files *)
  gen_install files
