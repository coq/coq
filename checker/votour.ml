(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Values

(** {6 Interactive visit of a vo} *)

type 'a repr =
| INT of int
| STRING of string
| BLOCK of int * 'a array
| OTHER

module type S =
sig
  type obj
  val input : in_channel -> obj
  val repr : obj -> obj repr
  val size : int list -> int
end

module Repr : S =
struct
  type obj = Obj.t

  let input chan =
    let obj = input_value chan in
    let () = CObj.register_shared_size obj in
    obj

  let repr obj =
    if Obj.is_block obj then
      let tag = Obj.tag obj in
      if tag = Obj.string_tag then STRING (Obj.magic obj)
      else if tag < Obj.no_scan_tag then
        let data = Obj.dup obj in
        let () = Obj.set_tag data 0 in
        BLOCK (tag, Obj.magic data)
      else OTHER
    else INT (Obj.magic obj)

  let size p = CObj.shared_size_of_pos p
end

(** Name of a value *)

let rec get_name ?(extra=false) = function
  |Any -> "?"
  |Fail s -> "Invalid node: "^s
  |Tuple (name,_) -> name
  |Sum (name,_,_) -> name
  |Array v -> "array"^(if extra then "/"^get_name ~extra v else "")
  |List v -> "list"^(if extra then "/"^get_name ~extra v else "")
  |Opt v -> "option"^(if extra then "/"^get_name ~extra v else "")
  |Int -> "int"
  |String -> "string"
  |Annot (s,v) -> s^"/"^get_name ~extra v
  |Dyn -> "<dynamic>"

(** For tuples, its quite handy to display the inner 1st string (if any).
    Cf. [structure_body] for instance *)

let get_string_in_tuple o =
  try
    for i = 0 to Array.length o - 1 do
      match Repr.repr o.(i) with
      | STRING s ->
        failwith (Printf.sprintf " [..%s..]" s)
      | _ -> ()
    done;
    ""
  with Failure s -> s

(** Some details : tags, integer value for non-block, etc etc *)

let rec get_details v o = match v, Repr.repr o with
  | (String | Any), STRING s ->
    Printf.sprintf " [%s]" (String.escaped s)
  |Tuple (_,v), BLOCK (_, o) -> get_string_in_tuple o
  |(Sum _|Any), BLOCK (tag, _) ->
    Printf.sprintf " [tag=%i]" tag
  |(Sum _|Any), INT i ->
    Printf.sprintf " [imm=%i]" i
  |Int, INT i -> Printf.sprintf " [imm=%i]" i
  |Annot (s,v), _ -> get_details v o
  |_ -> ""

let node_info (v,o,p) =
  get_name ~extra:true v ^ get_details v o ^
    " (size "^ string_of_int (Repr.size p)^"w)"

(** Children of a block : type, object, position.
    For lists, we collect all elements of the list at once *)

let access_children vs os pos =
  if Array.length os = Array.length vs then
    Array.mapi (fun i v -> v, os.(i), i::pos) vs
  else raise Exit

let access_list v o pos =
  let rec loop o pos = match Repr.repr o with
  | INT 0 -> []
  | BLOCK (0, [|hd; tl|]) ->
    (v, hd, 0 :: pos) :: loop tl (1 :: pos)
  | _ -> raise Exit
  in
  Array.of_list (loop o pos)

let access_block o = match Repr.repr o with
| BLOCK (tag, os) -> (tag, os)
| _ -> raise Exit
let access_int o = match Repr.repr o with INT i -> i | _ -> raise Exit

(** raises Exit if the object has not the expected structure *)
let rec get_children v o pos = match v with
  |Tuple (_, v) ->
    let (_, os) = access_block o in
    access_children v os pos
  |Sum (_, _, vv) ->
    begin match Repr.repr o with
    | BLOCK (tag, os) -> access_children vv.(tag) os pos
    | INT _ -> [||]
    | _ -> raise Exit
    end
  |Array v ->
    let (_, os) = access_block o in
    access_children (Array.make (Array.length os) v) os pos
  |List v -> access_list v o pos
  |Opt v ->
    begin match Repr.repr o with
    | INT 0 -> [||]
    | BLOCK (0, [|x|]) -> [|(v, x, 0 :: pos)|]
    | _ -> raise Exit
    end
  |String | Int -> [||]
  |Annot (s,v) -> get_children v o pos
  |Any -> raise Exit
  |Dyn ->
    begin match Repr.repr o with
    | BLOCK (0, [|id; o|]) ->
      let n = access_int id in
      let tpe = find_dyn n in
      [|(Int, id, 0 :: pos); (tpe, o, 1 :: pos)|]
    | _ -> raise Exit
    end
  |Fail s -> failwith "forbidden"

let get_children v o pos =
  try get_children v o pos
  with Exit -> match Repr.repr o with
  | BLOCK (_, os) -> Array.mapi (fun i o -> Any, o, i :: pos) os
  | _ -> [||]

type info = {
  nam : string;
  typ : value;
  obj : Repr.obj;
  pos : int list
}

let stk = ref ([] : info list)

let init () = stk := []

let push name v o p = stk := { nam = name; typ = v; obj = o; pos = p } :: !stk

let pop () = match !stk with
  | i::s -> stk := s; i
  | _ -> failwith "empty stack"

let rec visit v o pos =
  Printf.printf "\nDepth %d Pos %s Context %s\n"
    (List.length !stk)
    (String.concat "." (List.rev_map string_of_int pos))
    (String.concat "/" (List.rev_map (fun i -> i.nam) !stk));
  Printf.printf "-------------\n";
  let children = get_children v o pos in
  let nchild = Array.length children in
  Printf.printf "Here: %s, %d child%s\n"
    (node_info (v,o,pos)) nchild (if nchild = 0 then "" else "ren:");
  Array.iteri
    (fun i vop -> Printf.printf "  %d: %s\n" i (node_info vop))
    children;
  Printf.printf "-------------\n";
  Printf.printf ("# %!");
  let l = read_line () in
  try
    if l = "u" then let info = pop () in visit info.typ info.obj info.pos
    else if l = "x" then (Printf.printf "\nGoodbye!\n\n";exit 0)
    else
      let v',o',pos' = children.(int_of_string l) in
      push (get_name v) v o pos;
      visit v' o' pos'
  with
  | Failure "empty stack" -> ()
  | Failure "forbidden" -> let info = pop () in visit info.typ info.obj info.pos
  | Failure _ | Invalid_argument _ -> visit v o pos

(** Loading the vo *)

type segment = {
  name : string;
  mutable pos : int;
  typ : Values.value;
}

let visit_vo f =
  Printf.printf "\nWelcome to votour !\n";
  Printf.printf "Enjoy your guided tour of a Coq .vo or .vi file\n";
  Printf.printf "Object sizes are in words (%d bits)\n" Sys.word_size;
  Printf.printf
    "At prompt, <n> enters the <n>-th child, u goes up 1 level, x exits\n\n%!";
  let segments = [|
    {name="library"; pos=0; typ=Values.v_lib};
    {name="univ constraints of opaque proofs"; pos=0;typ=Values.v_univopaques}; 
    {name="discharging info"; pos=0; typ=Opt Any};
    {name="STM tasks"; pos=0; typ=Opt Values.v_stm_seg};
    {name="opaque proofs"; pos=0; typ=Values.v_opaques}; 
  |] in
  while true do
    let ch = open_in_bin f in
    let magic = input_binary_int ch in
    Printf.printf "File format: %d\n%!" magic;
    for i=0 to Array.length segments - 1 do
      let pos = input_binary_int ch in
      segments.(i).pos <- pos_in ch;
      seek_in ch pos;
      ignore(Digest.input ch);
    done;
    Printf.printf "The file has %d segments, choose the one to visit:\n"
      (Array.length segments);
    Array.iteri (fun i { name; pos } ->
      Printf.printf "  %d: %s, starting at byte %d\n" i name pos)
      segments;
    Printf.printf "# %!";
    let l = read_line () in
    let seg = int_of_string l in
    seek_in ch segments.(seg).pos;
    let o = Repr.input ch in
    let () = init () in
    visit segments.(seg).typ o []
  done

let main =
  if not !Sys.interactive then
    Arg.parse [] visit_vo
      ("votour: guided tour of a Coq .vo or .vi file\n"^
       "Usage: votour file.v[oi]")
