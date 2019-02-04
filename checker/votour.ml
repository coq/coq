(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Values

(** {6 Interactive visit of a vo} *)

let max_string_length = 1024

let rec read_num max =
  let quit () =
    Printf.printf "\nGoodbye!\n%!";
    exit 0 in
  Printf.printf "# %!";
  let l = try read_line () with End_of_file -> quit () in
  if l = "u" then None
  else if l = "x" then quit ()
  else
    match int_of_string l with
    | v ->
      if v < 0 || v >= max then
        let () =
          Printf.printf "Out-of-range input! (only %d children)\n%!" max in
        read_num max
      else Some v
    | exception Failure _ ->
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

  let memory = ref LargeArray.empty
  let sizes = ref LargeArray.empty
  (** size, in words *)

  let ws = Sys.word_size / 8

  let rec init_size seen k = function
  | Int _ | Atm _ | Fun _ -> k 0
  | Ptr p ->
    if LargeArray.get seen p then k 0
    else
      let () = LargeArray.set seen p true in
      match LargeArray.get !memory p with
      | Struct (tag, os) ->
        let len = Array.length os in
        let rec fold i accu k =
          if i == len then k accu
          else
            init_size seen (fun n -> fold (succ i) (accu + 1 + n) k) os.(i)
        in
        fold 0 1 (fun size -> let () = LargeArray.set !sizes p size in k size)
      | Int63 _ -> k 0
      | String s ->
        let size = 2 + (String.length s / ws) in
        let () = LargeArray.set !sizes p size in
        k size

  let size = function
  | Int _ | Atm _ | Fun _ -> 0
  | Ptr p -> LargeArray.get !sizes p

  let repr = function
  | Int i -> INT i
  | Atm t -> BLOCK (t, [||])
  | Fun _ -> OTHER
  | Ptr p ->
    match LargeArray.get !memory p with
    | Struct (tag, os) -> BLOCK (tag, os)
    | Int63 _ -> OTHER (* TODO: pretty-print int63 values *)
    | String s -> STRING s

  let input ch =
    let obj, mem = parse_channel ch in
    let () = memory := mem in
    let () = sizes := LargeArray.make (LargeArray.length mem) (-1) in
    let seen = LargeArray.make (LargeArray.length mem) false in
    let () = init_size seen ignore obj in
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
  | Proxy v -> get_name ~extra !v
  | Uint63 -> "Uint63"

(** For tuples, its quite handy to display the inner 1st string (if any).
    Cf. [structure_body] for instance *)

exception TupleString of string
let get_string_in_tuple o =
  try
    for i = 0 to Array.length o - 1 do
      match Repr.repr o.(i) with
      | STRING s ->
        let len = min max_string_length (String.length s) in
        raise (TupleString (Printf.sprintf " [..%s..]" (String.sub s 0 len)))
      | _ -> ()
    done;
    ""
  with TupleString s -> s

(** Some details : tags, integer value for non-block, etc etc *)

let rec get_details v o = match v, Repr.repr o with
  | (String | Any), STRING s ->
    let len = min max_string_length (String.length s) in
    Printf.sprintf " [%s]" (String.escaped (String.sub s 0 len))
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
  let rec loop o pos accu = match Repr.repr o with
  | INT 0 -> List.rev accu
  | BLOCK (0, [|hd; tl|]) ->
    loop tl (1 :: pos) ((v, hd, 0 :: pos) :: accu)
  | _ -> raise Exit
  in
  Array.of_list (loop o pos [])

let access_block o = match Repr.repr o with
| BLOCK (tag, os) -> (tag, os)
| _ -> raise Exit

(** raises Exit if the object has not the expected structure *)
exception Forbidden
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
  | String ->
    begin match Repr.repr o with
    | STRING _ -> [||]
    | _ -> raise Exit
    end
  | Int ->
    begin match Repr.repr o with
    | INT _ -> [||]
    | _ -> raise Exit
    end
  |Annot (s,v) -> get_children v o pos
  |Any -> raise Exit
  |Dyn ->
    begin match Repr.repr o with
    | BLOCK (0, [|id; o|]) ->
      let tpe = Any in
      [|(Int, id, 0 :: pos); (tpe, o, 1 :: pos)|]
    | _ -> raise Exit
    end
  |Fail s -> raise Forbidden
  | Proxy v -> get_children !v o pos
  | Uint63 -> raise Exit

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

exception EmptyStack
let pop () = match !stk with
  | i::s -> stk := s; i
  | _ -> raise EmptyStack

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
  | EmptyStack -> ()
  | Forbidden -> let info = pop () in visit info.typ info.obj info.pos
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
  let magic = really_input_string chan 4 in
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
    (* On 32-bit machines, representation may exceed the max size of arrays *)
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

let () =
  if not !Sys.interactive then
    Arg.parse [] visit_vo
      ("votour: guided tour of a Coq .vo or .vi file\n"^
       "Usage: votour file.v[oi]")
