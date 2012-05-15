(* The mingw32-ocaml cross-compiler currently uses Filename.dir_sep="/".
   Let's tweak that... *)

let _ = Filename.dir_sep.[0] <- '\\'
