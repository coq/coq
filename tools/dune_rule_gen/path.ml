(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

(* We distinguish Path arguments as to adjust for subdirs in Coq
   theory evaluation *)

type t = Rel of string | Abs of string

let to_string = function Rel p -> p | Abs p -> p

(* paths which begin with a dune variable are considered absolute
   (eg %{project_root}/bla) *)
let is_relative path =
  not (CString.is_prefix "%{" path) && Filename.is_relative path

let make path = if is_relative path then Rel path else Abs path

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
