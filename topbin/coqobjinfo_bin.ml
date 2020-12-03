(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Sexp :
sig
type t =
| Atom of string
| Node of t list

val print : out_channel -> t -> unit
end =
struct
type t =
| Atom of string
| Node of t list

let rec print chan = function
| Atom s -> Printf.fprintf chan "\"%s\"" (String.escaped s)
| Node n -> Printf.fprintf chan "(%a)" print_list n

and print_list chan = function
| [] -> ()
| [x] -> print chan x
| [x; y] ->
  Printf.fprintf chan "%a %a" print x print y
| x :: rem ->
  Printf.fprintf chan "%a %a" print x print_list rem

end

type 'a segment = { name : string; printer : 'a -> Sexp.t }

let parse file segs =
  let ch = ObjFile.open_in ~file in
  let fold accu seg =
    try
      let data, _ = ObjFile.marshal_in_segment ch ~segment:seg.name in
      Sexp.Node [Sexp.Atom seg.name; seg.printer data] :: accu
    with Not_found -> accu
  in
  try
    let data = List.fold_left fold [] segs in
    let () = ObjFile.close_in ch in
    data
  with e ->
    let () = ObjFile.close_in ch in
    raise e

(* TODO: share me with Stateid *)
type tasks = (int option, Obj.t) Stateid.request list * Obj.t

let pr_request (req : (int option, Obj.t) Stateid.request) =
  let open Stateid in
  Sexp.Node [
    Sexp.Atom req.kernel_name;
  ]

let pr_task = function
| None -> Sexp.Node []
| Some (tasks, _) ->
  Sexp.Node (List.map pr_request tasks)

let seg_task : tasks option segment = { name = "tasks"; printer = pr_task }

let () =
  let file = Sys.argv.(1) in
  let data = parse file [seg_task] in
  let () = Printf.printf "%a\n%!" Sexp.print (Sexp.Node data) in
  ()
