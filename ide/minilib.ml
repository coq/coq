(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** Some excerpt of Util and similar files to avoid loading the whole
    module and its dependencies (and hence Compat and Camlp4) *)

module Stringmap = Map.Make(String)

let list_fold_left_i f =
  let rec it_list_f i a = function
    | [] -> a
    | b::l -> it_list_f (i+1) (f i a b) l
  in
  it_list_f

(* [list_chop i l] splits [l] into two lists [(l1,l2)] such that
   [l1++l2=l] and [l1] has length [i].
   It raises [Failure] when [i] is negative or greater than the length of [l]  *)

let list_chop n l =
  let rec chop_aux i acc = function
    | tl when i=0 -> (List.rev acc, tl)
    | h::t -> chop_aux (pred i) (h::acc) t
    | [] -> failwith "list_chop"
  in
  chop_aux n [] l


let list_map_i f =
  let rec map_i_rec i = function
    | [] -> []
    | x::l -> let v = f i x in v :: map_i_rec (i+1) l
  in
  map_i_rec


let list_index x =
  let rec index_x n = function
    | y::l -> if x = y then n else index_x (succ n) l
    | [] -> raise Not_found
  in
  index_x 1

let list_index0 x l = list_index x l - 1

let list_filter_i p =
  let rec filter_i_rec i = function
    | [] -> []
    | x::l -> let l' = filter_i_rec (succ i) l in if p i x then x::l' else l'
  in
  filter_i_rec 0

let string_map f s =
  let l = String.length s in
  let r = String.create l in
  for i= 0 to (l - 1) do r.[i] <- f (s.[i]) done;
  r

let subst_command_placeholder s t =
  Str.global_replace (Str.regexp_string "%s") t s

let path_to_list p =
  let sep = Str.regexp (if Sys.os_type = "Win32" then ";" else ":") in
    Str.split sep p

(* On win32, the home directory is probably not in $HOME, but in
   some other environment variable *)

let home =
  try Sys.getenv "HOME" with Not_found ->
    try (Sys.getenv "HOMEDRIVE")^(Sys.getenv "HOMEPATH") with Not_found ->
      try Sys.getenv "USERPROFILE" with Not_found -> Filename.current_dir_name

let xdg_config_home =
  try
    Filename.concat (Sys.getenv "XDG_CONFIG_HOME") "coq"
  with Not_found ->
    Filename.concat home "/.config/coq"

let xdg_config_dirs =
  xdg_config_home :: (try
    List.map (fun dir -> Filename.concat dir "coq") (path_to_list (Sys.getenv "XDG_CONFIG_DIRS"))
  with Not_found -> ["/etc/xdg/coq"])@(match Coq_config.configdir with |None -> [] |Some d -> [d])

let xdg_data_home =
  try
    Filename.concat (Sys.getenv "XDG_DATA_HOME") "coq"
  with Not_found ->
    Filename.concat home "/.local/share/coq"

let xdg_data_dirs =
  xdg_data_home :: (try
    List.map (fun dir -> Filename.concat dir "coq") (path_to_list (Sys.getenv "XDG_DATA_DIRS"))
  with Not_found ->
    ["/usr/local/share/coq";"/usr/share/coq"])@(match Coq_config.datadir with |None -> [] |Some d -> [d])

let coqtop_path = ref ""

(* On a Win32 application with no console, writing to stderr raise
   a Sys_error "bad file descriptor", hence the "try" below.
   Ideally, we should re-route message to a log file somewhere, or
   print in the response buffer.
*)

let safe_prerr_endline s =
  try prerr_endline s;flush stderr with _ -> ()

(* Hints to partially detects if two paths refer to the same repertory *)
let rec remove_path_dot p =
  let curdir = Filename.concat Filename.current_dir_name "" in (* Unix: "./" *)
  let n = String.length curdir in
  let l = String.length p in
  if l > n && String.sub p 0 n = curdir then
    let n' =
      let sl = String.length Filename.dir_sep in
      let i = ref n in
	while !i <= l - sl && String.sub p !i sl = Filename.dir_sep do i := !i + sl done; !i in
    remove_path_dot (String.sub p n' (l - n'))
  else
    p

let strip_path p =
  let cwd = Filename.concat (Sys.getcwd ()) "" in (* Unix: "`pwd`/" *)
  let n = String.length cwd in
  let l = String.length p in
  if l > n && String.sub p 0 n = cwd then
    let n' =
      let sl = String.length Filename.dir_sep in
      let i = ref n in
	while !i <= l - sl && String.sub p !i sl = Filename.dir_sep do i := !i + sl done; !i in
    remove_path_dot (String.sub p n' (l - n'))
  else
    remove_path_dot p

let canonical_path_name p =
  let current = Sys.getcwd () in
  try
    Sys.chdir p;
    let p' = Sys.getcwd () in
    Sys.chdir current;
    p'
  with Sys_error _ ->
    (* We give up to find a canonical name and just simplify it... *)
    strip_path p

let correct_path f dir = if Filename.is_relative f then Filename.concat dir f else f

(*
  checks if two file names refer to the same (existing) file by
  comparing their device and inode.
  It seems that under Windows, inode is always 0, so we cannot
  accurately check if

*)
(* Optimised for partial application (in case many candidates must be
   compared to f1). *)
let same_file f1 =
  try
    let s1 = Unix.stat f1 in
    (fun f2 ->
      try
        let s2 = Unix.stat f2 in
        s1.Unix.st_dev = s2.Unix.st_dev &&
          if Sys.os_type = "Win32" then f1 = f2
          else s1.Unix.st_ino = s2.Unix.st_ino
      with
          Unix.Unix_error _ -> false)
  with
      Unix.Unix_error _ -> (fun _ -> false)
