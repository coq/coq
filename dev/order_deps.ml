(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* usage: order_deps <name1> <name2> ...

read from stdin a set of dependencies in make format, that is,
lines of the form:

   name1: name2 ... namek (with k >= 0)

print on stdout all dependencies for <name1> <name2> ...
in compilation order (from the less dependent to the most dependent)

detect cycles *)

open Str
open Hashtbl
open List

let pr = print_endline
let pri n = print_int n; print_newline()

let get_line() =
  let res = ref "" in
    try
      while !res = "" do res := read_line() done;
      while last_chars !res 1 = "\\" do
	!res.[String.length !res - 1] <- ' ';
	res := !res ^ (read_line())
      done; !res
    with End_of_file ->
      if !res = "" then raise End_of_file else !res

let str_neq s s' = String.compare s s' <> 0

module Set = Set.Make(String)

let depth tbl s =
  try fst (Hashtbl.find tbl s)
  with Not_found -> Some 0

let dependancies tbl s =
  try snd (Hashtbl.find tbl s)
  with Not_found -> Set.empty

let build_table() =
  let tbl = Hashtbl.create 117 in
    try
      while true do
	let s = get_line() in
	  try
	    begin
	      let _ = search_forward (regexp "\\.cm[oi]:") s 0 in
              let s = global_replace (regexp "\\.cm.") ".cmo" s in
		match Str.split (regexp "[ :]+") s with
		  | s::l ->
		      let add set s = Set.add s set in
		      let set = List.fold_left add (dependancies tbl s) l in
			Hashtbl.replace tbl s (None,Set.remove s set)
		  | _ -> ()
	    end
	  with Not_found -> ()
      done; tbl
    with End_of_file -> tbl

let pr_name s = print_string (s ^ " ")

(*
let pr_elt s = function
  | Some d,set ->
      print_int d; print_string " "; pr_name s; Set.iter pr_name set;
      print_newline()
  | _,set ->
      print_string "? "; pr_name s; Set.iter pr_name set;
      print_newline()

let prt tbl = Hashtbl.iter pr_elt tbl
*)

exception No_max

let find_max =
  let v = ref 0 in
  fun tbl ->
    let compute_max s =
      match depth tbl s with
	| Some d -> if d >= !v then v:=d
	| _ -> raise No_max
    in
      fun set ->
	v:=0;
	try Set.iter compute_max set; Some (!v+1)
	with No_max -> None

let comp_depth tbl s1 s2 =
  match depth tbl s1, depth tbl s2 with
    | Some d1, Some d2 -> Pervasives.compare d1 d2
    | None, _ -> 1
    | _ -> -1

let concat_deps tbl set =
  let add_deps s set = Set.add s (Set.union (dependancies tbl s) set) in
  Set.fold add_deps set Set.empty

let compute_depth tbl s = function
  | None,set ->
      let dopt = find_max tbl set in
	if dopt <> None then Hashtbl.replace tbl s (dopt,concat_deps tbl set)
  | _ -> ()

let none_number tbl =
  let n = ref 0 in
  let check s = function
    | None,_ -> incr n
    | _ -> ()
  in Hashtbl.iter check tbl; !n

let none_number_decrease tbl n =
  let n' = none_number tbl in
    if n' < !n then (n := n'; true) else false

(*
let pr_name' tbl s =
  let value = function Some x -> x | None -> 0 in
    print_int (value (depth tbl s)); print_string (" " ^ s ^ " ")
*)

let main() =
  if Array.length Sys.argv < 2 then
    (prerr_endline ("usage: " ^ Sys.argv.(0) ^ " <filename> ..."); exit 1);
  let tbl = build_table()
  and args = Set.remove Sys.argv.(0)
	       (Array.fold_right Set.add Sys.argv Set.empty) in
  let files = ref args and n = ref (none_number tbl) in
    Hashtbl.iter (compute_depth tbl) tbl;
    while not (Set.is_empty !files) & none_number_decrease tbl n do
      files := Set.filter (fun s -> depth tbl s = None) !files;
      Hashtbl.iter (compute_depth tbl) tbl
    done;
    if not (Set.is_empty !files) then
      (prerr_endline "error: cyclic dependancies!"; exit 1);
    let l = Set.elements (concat_deps tbl args) in
    let l = List.sort (comp_depth tbl) l in
      List.iter pr_name l; print_newline()

let _ = main()
