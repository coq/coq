(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

(* We distinguish Path arguments as to adjust for subdirs in Coq
   theory evaluation *)

type t = Rel of string | Abs of string

let to_string = function Rel p -> p | Abs p -> p

let make path =
  if Filename.is_relative path then
    (* when called by dune, the cmxs and META files are in
       ../install/... relative to cwd (= _build/default)
       but the generated dune file will be moved to ../theories
       so adjusting the path to be relative to the .v won't work

       (it would be relative to the .v in
       project_root/_build/default/theories but dune would read it as
       relative to the .v in project_root/theories, the number of ..
       to insert to get to project_root doesn't match) *)
    if CString.is_prefix ".." path then
      Abs (Filename.concat "%{project_root}" @@
           Filename.concat "_build" @@
           String.sub path 3 (String.length path - 3))
    else
      Rel path
  else
    Abs path

let map ~f = function Rel p -> Rel (f p) | Abs p -> Abs (f p)

let fold ~f = function Rel p -> f p | Abs p -> f p

let relative dir path = map dir ~f:(fun dir -> Filename.concat dir path)

let gen_sub n = String.concat Filename.dir_sep @@ List.init n (fun _ -> "..")

let adjust ~lvl = function
  | Rel path -> Rel (Filename.concat (gen_sub lvl) path)
  | Abs path -> Abs path

let compare p1 p2 = match p1, p2 with
  | Rel p1, Rel p2 -> String.compare p1 p2
  | Abs p1, Abs p2 -> String.compare p1 p2
  | Rel _, Abs _ -> -1
  | Abs _, Rel _ -> 1

let pp fmt = function
  | Rel p -> Format.fprintf fmt "%s" p
  | Abs p -> Format.fprintf fmt "%s" p

let basename = fold ~f:Filename.basename

let add_extension ~ext = map ~f:(fun p -> p ^ ext)

let replace_ext ~ext = map ~f:(fun p -> Filename.remove_extension p ^ ext)

(* Coqdep strips files with dirname "." of the basename, so we need
   to fixup that until we can fix coqdep... [fixing coqdep breaks dune] *)
let coqdep_fixup_dir = function
  | Abs file -> Abs file
  | Rel file ->
    match Filename.dirname file with
    | "." -> Rel (Filename.basename file)
    | _ -> Rel file
