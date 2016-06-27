(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Values

(** {6 Interactive visit of a vo} *)

let rec read_num max =
  let quit () =
    Printf.printf "\nGoodbye!\n%!";
    exit 0 in
  Printf.printf "# %!";
  let l = try read_line () with End_of_file -> quit () in
  if l = "u" then None
  else if l = "x" then quit ()
  else
    try
      let v = int_of_string l in
      if v < 0 || v >= max then
        let () =
          Printf.printf "Out-of-range input! (only %d children)\n%!" max in
        read_num max
      else Some v
    with Failure "int_of_string" ->
      Printf.printf "Unrecognized input! <n> enters the <n>-th child, u goes up 1 level, x exits\n%!";
      read_num max

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
  val size : obj -> int
  val oid : obj -> int option
end

module ReprObj : S =
struct
  type obj = Obj.t * int list

  let input chan =
    let obj = input_value chan in
    let () = CObj.register_shared_size obj in
    (obj, [])

  let repr (obj, pos) =
    if Obj.is_block obj then
      let tag = Obj.tag obj in
      if tag = Obj.string_tag then STRING (Obj.magic obj)
      else if tag < Obj.no_scan_tag then
        let init i = (Obj.field obj i, i :: pos) in
        let data = Array.init (Obj.size obj) init in
        BLOCK (tag, Obj.magic data)
      else OTHER
    else INT (Obj.magic obj)

  let size (_, p) = CObj.shared_size_of_pos p
  let oid _ = None
end

module ReprMem : S =
struct
  open Analyze

  type obj = data

  let memory = ref [||]
  let sizes = ref [||]
  (** size, in words *)

  let ws = Sys.word_size / 8

  let rec init_size seen = function
  | Int _ | Atm _ | Fun _ -> 0
  | Ptr p ->
    if seen.(p) then 0
    else
      let () = seen.(p) <- true in
      match (!memory).(p) with
      | Struct (tag, os) ->
        let fold accu o = accu + 1 + init_size seen o in
        let size = Array.fold_left fold 1 os in
        let () = (!sizes).(p) <- size in
        size
      | String s ->
        let size = 2 + (String.length s / ws) in
        let () = (!sizes).(p) <- size in
        size

  let size = function
  | Int _ | Atm _ | Fun _ -> 0
  | Ptr p -> (!sizes).(p)

  let repr = function
  | Int i -> INT i
  | Atm t -> BLOCK (t, [||])
  | Fun _ -> OTHER
  | Ptr p ->
    match (!memory).(p) with
    | Struct (tag, os) -> BLOCK (tag, os)
    | String s -> STRING s

  let input ch =
    let obj, mem = parse_channel ch in
    let () = memory := mem in
    let () = sizes := Array.make (Array.length mem) (-1) in
    let seen = Array.make (Array.length mem) false in
    let _ = init_size seen obj in
    obj

  let oid = function
  | Int _ | Atm _ | Fun _ -> None
  | Ptr p -> Some p
end

module Visit (Repr : S) :
sig
  val init : unit -> unit
  val visit : Values.value -> Repr.obj -> int list -> unit
end =
struct

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

let get_oid obj = match Repr.oid obj with
| None -> ""
| Some id -> Printf.sprintf " [0x%08x]" id

let node_info (v,o,p) =
  get_name ~extra:true v ^ get_details v o ^
    " (size "^ string_of_int (Repr.size o)^"w)" ^ get_oid o

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
  try
    match read_num (Array.length children) with
    | None -> let info = pop () in visit info.typ info.obj info.pos
    | Some child ->
       let v',o',pos' = children.(child) in
       push (get_name v) v o pos;
       visit v' o' pos'
  with
  | Failure "empty stack" -> ()
  | Failure "forbidden" -> let info = pop () in visit info.typ info.obj info.pos
  | Failure _ | Invalid_argument _ -> visit v o pos

end

(** Loading the vo *)

type header = {
  magic : string;
  (** Magic number of the marshaller *)
  length : int;
  (** Size on disk in bytes *)
  size32 : int;
  (** Size in words when loaded on 32-bit systems *)
  size64 : int;
  (** Size in words when loaded on 64-bit systems *)
  objects : int;
  (** Number of blocks defined in the marshalled structure *)
}

let dummy_header = {
  magic = "\000\000\000\000";
  length = 0;
  size32 = 0;
  size64 = 0;
  objects = 0;
}

let parse_header chan =
  let magic = String.create 4 in
  let () = for i = 0 to 3 do magic.[i] <- input_char chan done in
  let length = input_binary_int chan in
  let objects = input_binary_int chan in
  let size32 = input_binary_int chan in
  let size64 = input_binary_int chan in
  { magic; length; size32; size64; objects }

type segment = {
  name : string;
  mutable pos : int;
  typ : Values.value;
  mutable header : header;
}

let make_seg name typ = { name; typ; pos = 0; header = dummy_header }

let visit_vo f =
  Printf.printf "\nWelcome to votour !\n";
  Printf.printf "Enjoy your guided tour of a Coq .vo or .vi file\n";
  Printf.printf "Object sizes are in words (%d bits)\n" Sys.word_size;
  Printf.printf
    "At prompt, <n> enters the <n>-th child, u goes up 1 level, x exits\n\n%!";
  let segments = [|
    make_seg "summary" Values.v_libsum;
    make_seg "library" Values.v_lib;
    make_seg "univ constraints of opaque proofs" Values.v_univopaques;
    make_seg "discharging info" (Opt Any);
    make_seg "STM tasks" (Opt Values.v_stm_seg);
    make_seg "opaque proofs" Values.v_opaques;
  |] in
  let repr =
    if Sys.word_size = 64 then (module ReprMem : S) else (module ReprObj : S)
    (** On 32-bit machines, representation may exceed the max size of arrays *)
  in
  let module Repr = (val repr : S) in
  let module Visit = Visit(Repr) in
  while true do
    let ch = open_in_bin f in
    let magic = input_binary_int ch in
    Printf.printf "File format: %d\n%!" magic;
    for i=0 to Array.length segments - 1 do
      let pos = input_binary_int ch in
      segments.(i).pos <- pos_in ch;
      let header = parse_header ch in
      segments.(i).header <- header;
      seek_in ch pos;
      ignore(Digest.input ch);
    done;
    Printf.printf "The file has %d segments, choose the one to visit:\n"
      (Array.length segments);
    Array.iteri (fun i { name; pos; header } ->
      let size = if Sys.word_size = 64 then header.size64 else header.size32 in
      Printf.printf "  %d: %s, starting at byte %d (size %iw)\n" i name pos size)
      segments;
    match read_num (Array.length segments) with
    | Some seg ->
       seek_in ch segments.(seg).pos;
       let o = Repr.input ch in
       let () = Visit.init () in
       Visit.visit segments.(seg).typ o []
    | None -> ()
  done

let main =
  if not !Sys.interactive then
    Arg.parse [] visit_vo
      ("votour: guided tour of a Coq .vo or .vi file\n"^
       "Usage: votour file.v[oi]")
