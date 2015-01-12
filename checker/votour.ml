(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Values

(** {6 Interactive visit of a vo} *)

(** Name of a value *)

type dyn = { dyn_tag : string; dyn_obj : Obj.t; }

let to_dyn obj = (Obj.magic obj : dyn)

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

let get_string_in_tuple v o =
  try
    for i = 0 to Array.length v - 1 do
      if v.(i) = String then
        failwith (" [.."^(Obj.magic (Obj.field o i) : string)^"..]");
    done;
    ""
  with Failure s -> s

(** Some details : tags, integer value for non-block, etc etc *)

let rec get_details v o = match v with
  |String | Any when (Obj.is_block o && Obj.tag o = Obj.string_tag) ->
    " [" ^ String.escaped (Obj.magic o : string) ^"]"
  |Tuple (_,v) -> get_string_in_tuple v o
  |(Sum _|Any) when Obj.is_block o ->
    " [tag=" ^ string_of_int (Obj.tag o) ^"]"
  |(Sum _|Any) ->
    " [imm=" ^ string_of_int (Obj.magic o : int) ^"]"
  |Int -> " [" ^ string_of_int (Obj.magic o : int) ^"]"
  |Annot (s,v) -> get_details v o
  |_ -> ""

let node_info (v,o,p) =
  get_name ~extra:true v ^ get_details v o ^
    " (size "^ string_of_int (CObj.shared_size_of_pos p)^"w)"

(** Children of a block : type, object, position.
    For lists, we collect all elements of the list at once *)

let access_children vs o pos =
  Array.mapi (fun i v -> v, Obj.field o i, i::pos) vs

let rec get_children v o pos = match v with
  |Tuple (_,v) -> access_children v o pos
  |Sum (_,_,vv) ->
    if Obj.is_block o then access_children vv.(Obj.tag o) o pos
    else [||]
  |Array v -> access_children (Array.make (Obj.size o) v) o pos
  |List v ->
    let rec loop pos = function
      | [] -> []
      | o :: ol -> (v,o,0::pos) :: loop (1::pos) ol
    in
    Array.of_list (loop pos (Obj.magic o : Obj.t list))
  |Opt v ->
    if Obj.is_block o then [|v,Obj.field o 0,0::pos|] else [||]
  |String | Int -> [||]
  |Annot (s,v) -> get_children v o pos
  |Any ->
    if Obj.is_block o && Obj.tag o < Obj.no_scan_tag then
      Array.init (Obj.size o) (fun i -> (Any,Obj.field o i,i::pos))
    else [||]
  |Dyn ->
    let t = to_dyn o in
    let tpe = find_dyn t.dyn_tag in
    [|(String, Obj.repr t.dyn_tag, 0 :: pos); (tpe, t.dyn_obj, 1 :: pos)|]
  |Fail s -> failwith "forbidden"

type info = {
  nam : string;
  typ : value;
  obj : Obj.t;
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
    {name="STM tasks"; pos=0; typ=Opt Any};
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
    let o = (input_value ch : Obj.t) in
    let () = CObj.register_shared_size o in
    let () = init () in
    visit segments.(seg).typ o []
  done

let main =
  if not !Sys.interactive then
    Arg.parse [] visit_vo
      ("votour: guided tour of a Coq .vo or .vi file\n"^
       "Usage: votour file.v[oi]")
