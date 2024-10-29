(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Values

(** {6 Interactive visit of a vo} *)

let max_string_length = 1024

type command =
| CmdParent
| CmdChild of int
| CmdSort
| CmdList
| CmdHelp
| CmdExit

let help () =
  Printf.printf "Help\n\
  <n>\tenter the <n>-th child\n\
  u\tgo up 1 level\n\
  s\tsort\n\
  l\ttreat current node as a list\n\
  x\texit\n\n%!"

let quit () =
  Printf.printf "\nGoodbye!\n%!";
  exit 0

let rec read_num max =
  Printf.printf "# %!";
  let l = try read_line () with End_of_file -> quit () in
  match l with
  | "u" -> CmdParent
  | "s" -> CmdSort
  | "x" -> CmdExit
  | "h" -> CmdHelp
  | "l" -> CmdList
  | _ ->
    match int_of_string l with
    | v ->
      if v < 0 || v >= max then
        let () =
          Printf.printf "Out-of-range input! (only %d children)\n%!" max in
        read_num max
      else CmdChild v
    | exception Failure _ ->
      Printf.printf "Unrecognized input! Input h for help\n%!";
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
      | Int64 _ -> k 0
      | Float64 _ -> k 0
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
    | Int64 _ -> OTHER (* TODO: pretty-print int63 values *)
    | Float64 _ -> OTHER (* TODO: pretty-print float64 values *)
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

let rec get_name ?(extra=false) v = match kind v with
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
  | Int64 -> "Int64"
  | Float64 -> "Float64"

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

let rec get_details v o = match kind v, Repr.repr o with
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
  else raise_notrace Exit

let access_list v o pos =
  let rec loop o pos accu = match Repr.repr o with
  | INT 0 -> List.rev accu
  | BLOCK (0, [|hd; tl|]) ->
    loop tl (1 :: pos) ((v, hd, 0 :: pos) :: accu)
  | _ -> raise_notrace Exit
  in
  Array.of_list (loop o pos [])

let access_block o = match Repr.repr o with
| BLOCK (tag, os) -> (tag, os)
| _ -> raise_notrace Exit

(** raises Exit if the object has not the expected structure *)
exception Forbidden
let rec get_children v o pos = match kind v with
  |Tuple (_, v) ->
    let (_, os) = access_block o in
    access_children v os pos
  |Sum (_, _, vv) ->
    begin match Repr.repr o with
    | BLOCK (tag, os) -> access_children vv.(tag) os pos
    | INT _ -> [||]
    | _ -> raise_notrace Exit
    end
  |Array v ->
    let (_, os) = access_block o in
    access_children (Array.make (Array.length os) v) os pos
  |List v -> access_list v o pos
  |Opt v ->
    begin match Repr.repr o with
    | INT 0 -> [||]
    | BLOCK (0, [|x|]) -> [|(v, x, 0 :: pos)|]
    | _ -> raise_notrace Exit
    end
  | String ->
    begin match Repr.repr o with
    | STRING _ -> [||]
    | _ -> raise_notrace Exit
    end
  | Int ->
    begin match Repr.repr o with
    | INT _ -> [||]
    | _ -> raise_notrace Exit
    end
  |Annot (s,v) -> get_children v o pos
  |Any -> raise_notrace Exit
  | Fail s -> raise Forbidden
  | Int64 -> raise_notrace Exit
  | Float64 -> raise_notrace Exit

let get_children v o pos =
  try get_children v o pos
  with Exit -> match Repr.repr o with
  | BLOCK (_, os) -> Array.mapi (fun i o -> v_any, o, i :: pos) os
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

let print_state v o pos children =
  Printf.printf "\nDepth %d Pos %s Context %s\n"
    (List.length !stk)
    (String.concat "." (List.rev_map string_of_int pos))
    (String.concat "/" (List.rev_map (fun i -> i.nam) !stk));
  Printf.printf "-------------\n";
  let nchild = Array.length children in
  Printf.printf "Here: %s, %d child%s\n"
    (node_info (v,o,pos)) nchild (if nchild = 0 then "" else "ren:");
  Array.iter
    (fun (i, vop) -> Printf.printf "  %d: %s\n" i (node_info vop))
    children;
  Printf.printf "-------------\n"

let rec visit v o pos =
  let children = get_children v o pos in
  let children = Array.mapi (fun i vop -> (i, vop)) children in
  let () = print_state v o pos children in
  read_command v o pos children

and read_command v o pos children =
  try
    match read_num (Array.length children) with
    | CmdParent -> let info = pop () in visit info.typ info.obj info.pos
    | CmdChild child ->
       let _, (v',o',pos') = children.(child) in
       push (get_name v) v o pos;
       visit v' o' pos'
    | CmdSort ->
      let children = get_children v o pos in
      let children = Array.mapi (fun i vop -> (i, vop)) children in
      let sort (_, (_, o, _)) (_, (_, o', _)) =
        Int.compare (Repr.size o) (Repr.size o')
      in
      let sorted = Array.copy children in
      let () = Array.sort sort sorted in
      let () = print_state v o pos sorted in
      read_command v o pos children
    | CmdList -> visit (v_list v_any) o pos
    | CmdHelp ->
      let () = help () in
      read_command v o pos children
    | CmdExit -> quit ()
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

module ObjFile =
struct

type segment = {
  name : string;
  pos : int64;
  len : int64;
  hash : Digest.t;
  mutable header : header;
}

let input_int32 ch =
  let accu = ref 0l in
  for _i = 0 to 3 do
    let c = input_byte ch in
    accu := Int32.add (Int32.shift_left !accu 8) (Int32.of_int c)
  done;
  !accu

let input_int64 ch =
  let accu = ref 0L in
  for _i = 0 to 7 do
    let c = input_byte ch in
    accu := Int64.add (Int64.shift_left !accu 8) (Int64.of_int c)
  done;
  !accu

let input_segment_summary ch =
  let nlen = input_int32 ch in
  let name = really_input_string ch (Int32.to_int nlen) in
  let pos = input_int64 ch in
  let len = input_int64 ch in
  let hash = Digest.input ch in
  { name; pos; len; hash; header = dummy_header }

let rec input_segment_summaries ch n accu =
  if Int32.equal n 0l then Array.of_list (List.rev accu)
  else
    let s = input_segment_summary ch in
    let accu = s :: accu in
    input_segment_summaries ch (Int32.pred n) accu

let parse_segments ch =
  let magic = input_int32 ch in
  let version = input_int32 ch in
  let summary_pos = input_int64 ch in
  let () = LargeFile.seek_in ch summary_pos in
  let nsum = input_int32 ch in
  let seg = input_segment_summaries ch nsum [] in
  for i = 0 to Array.length seg - 1 do
    let () = LargeFile.seek_in ch seg.(i).pos in
    let header = parse_header ch in
    seg.(i).header <- header
  done;
  (magic, version, seg)

end

let visit_vo f =
  Printf.printf "\nWelcome to votour !\n";
  Printf.printf "Enjoy your guided tour of a Rocq .vo or .vi file\n";
  Printf.printf "Object sizes are in words (%d bits)\n" Sys.word_size;
  Printf.printf "Input h for help\n\n%!";
  let known_segments = [
    "summary", Values.v_libsum;
    "library", Values.v_lib;
    "opaques", Values.v_opaquetable;
    "vmlibrary", Values.v_vmlib;
  ] in
  let repr =
    if Sys.word_size = 64 then (module ReprMem : S) else (module ReprObj : S)
    (* On 32-bit machines, representation may exceed the max size of arrays *)
  in
  let module Repr = (val repr : S) in
  let module Visit = Visit(Repr) in
  while true do
    let ch = open_in_bin f in
    let (_magic, version, segments) = ObjFile.parse_segments ch in
    Printf.printf "File format: %ld\n%!" version;
    Printf.printf "The file has %d segments, choose the one to visit:\n"
      (Array.length segments);
    Array.iteri (fun i ObjFile.{ name; pos; header } ->
      let size = if Sys.word_size = 64 then header.size64 else header.size32 in
      Printf.printf "  %d: %s, starting at byte %Ld (size %iw)\n" i name pos size)
      segments;
    match read_num (Array.length segments) with
    | CmdChild seg ->
       let seg = segments.(seg) in
       let open ObjFile in
       LargeFile.seek_in ch seg.pos;
       let o = Repr.input ch in
       let () = Visit.init () in
       let typ = try List.assoc seg.name known_segments with Not_found -> v_any in
       Visit.visit typ o []
    | CmdParent | CmdSort | CmdList -> ()
    | CmdHelp ->
      help ()
    | CmdExit ->
      quit ()
  done

let () =
  if not !Sys.interactive then
    Arg.parse [] visit_vo
      ("votour: guided tour of a Rocq .vo or .vi file\n"^
       "Usage: votour file.v[oi]")
