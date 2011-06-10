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

(* On win32, the home directory is probably not in $HOME, but in
   some other environment variable *)

let home =
  try Sys.getenv "HOME" with Not_found ->
    try (Sys.getenv "HOMEDRIVE")^(Sys.getenv "HOMEPATH") with Not_found ->
      try Sys.getenv "USERPROFILE" with Not_found -> "."

let coqlib = ref ""
let coqtop_path = ref ""
