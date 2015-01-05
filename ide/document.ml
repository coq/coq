(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

exception Empty

let invalid_arg s = raise (Invalid_argument ("Document."^s))

type 'a sentence = { mutable state_id : Stateid.t option; data : 'a }

type id = Stateid.t

class type ['a] signals =
  object
    method popped : callback:('a -> unit) -> unit
    method pushed : callback:('a -> unit) -> unit
  end

class ['a] signal () =
object
  val mutable attached : ('a -> unit) list = []
  method call (x : 'a) =
    let iter f = try f x with _ -> () in
    List.iter iter attached
  method connect f = attached <- f :: attached
end

type 'a document = {
  mutable stack : 'a sentence list;
  mutable context : ('a sentence list * 'a sentence list) option;
  pushed_sig : 'a signal;
  popped_sig : 'a signal;
}

let connect d =
  object
    method pushed ~callback = d.pushed_sig#connect callback
    method popped ~callback = d.popped_sig#connect callback
  end

let create () = {
  stack = [];
  context = None;
  pushed_sig = new signal ();
  popped_sig = new signal ();
}

(* Invariant, only the tip is a allowed to have state_id = None *)
let invariant l = l = [] || (List.hd l).state_id <> None

let tip = function
  | { stack = [] } -> raise Empty
  | { stack = { state_id = Some id }::_ } -> id
  | { stack = { state_id = None }::_ } -> invalid_arg "tip"
  
let tip_data = function
  | { stack = [] } -> raise Empty
  | { stack = { data }::_ } -> data

let push d x =
  assert(invariant d.stack);
  d.stack <- { data = x; state_id = None } :: d.stack;
  d.pushed_sig#call x

let pop = function
  | { stack = [] } -> raise Empty
  | { stack = { data }::xs } as s -> s.stack <- xs; s.popped_sig#call data; data
  
let focus d ~cond_top:c_start ~cond_bot:c_stop =
  assert(invariant d.stack);
  if d.context <> None then invalid_arg "focus";
  let rec aux (a,s,b) grab = function
    | [] -> invalid_arg "focus"
    | { state_id = Some id; data } as x :: xs when not grab ->
        if c_start id data then aux (a,s,b) true (x::xs)
        else aux (x::a,s,b) grab xs
    | { state_id = Some id; data } as x :: xs ->
        if c_stop id data then List.rev a, List.rev (x::s), xs
        else aux (a,x::s,b) grab xs 
    | _ -> assert false in
  let a, s, b = aux ([],[],[]) false d.stack in
  d.stack <- s;
  d.context <- Some (a, b)
  
let unfocus = function
  | { context = None } -> invalid_arg "unfocus"
  | { context = Some (a,b); stack } as d ->
       assert(invariant stack);
       d.context <- None;
       d.stack <- a @ stack @ b
  
let focused { context } = context <> None

let to_lists = function
  | { context = None; stack = s } -> [],s,[]
  | { context = Some (a,b); stack = s } -> a,s,b

let flat f b = fun x -> f b x.state_id x.data

let find d f =
  let a, s, b = to_lists d in
  (
  try List.find (flat f false) a with Not_found ->
  try List.find (flat f true)  s with Not_found ->
      List.find (flat f false) b
  ).data
  
let find_map d f =
  let a, s, b = to_lists d in
  try CList.find_map (flat f false) a with Not_found -> 
  try CList.find_map (flat f true)  s with Not_found -> 
      CList.find_map (flat f false) b
  
let is_empty = function
  | { stack = []; context = None } -> true
  | _ -> false
  
let context d =
  let top, _, bot = to_lists d in
  let pair _ x y = try Option.get x, y with Option.IsNone -> assert false in
  List.map (flat pair true) top, List.map (flat pair true) bot

let iter d f =
  let a, s, b = to_lists d in
  List.iter (flat f false) a;
  List.iter (flat f true)  s;
  List.iter (flat f false) b
  
let stateid_opt_equal = Option.equal Stateid.equal

let is_in_focus d id =
  let _, focused, _ = to_lists d in
  List.exists (fun { state_id } -> stateid_opt_equal state_id (Some id)) focused

let print d f =
  let top, mid, bot = to_lists d in
  let open Pp in
  v 0
    (List.fold_right (fun i acc -> acc ++ cut() ++ flat f false i) top
    (List.fold_right (fun i acc -> acc ++ cut() ++ flat f true i)  mid
    (List.fold_right (fun i acc -> acc ++ cut() ++ flat f false i) bot (mt()))))

let assign_tip_id d id =
  match d with
  | { stack = { state_id = None } as top :: _ } -> top.state_id <- Some id
  | _ -> invalid_arg "assign_tip_id"

let cut_at d id =
  let aux (n, zone) { state_id; data } =
    if stateid_opt_equal state_id (Some id) then CSig.Stop (n, zone)
    else CSig.Cont (n + 1, data :: zone) in
  let n, zone = CList.fold_left_until aux (0, []) d.stack in
  for i = 1 to n do ignore(pop d) done;
  List.rev zone

let find_id d f =
  let top, focus, bot = to_lists d in
  let pred = function
    | { state_id = Some id; data } when f id data -> Some id
    | _ -> None in
  try CList.find_map pred top, true with Not_found ->
  try CList.find_map pred focus, false with Not_found ->
      CList.find_map pred bot, true

let before_tip d =
  let _, focused, rest = to_lists d in
  match focused with
  | _:: { state_id = Some id } :: _ -> id, false
  | _:: { state_id = None } :: _ -> assert false
  | [] -> raise Not_found
  | [_] ->
      match rest with
      | { state_id = Some id } :: _ -> id, true
      | { state_id = None } :: _ -> assert false
      | [] -> raise Not_found

let fold_all d a f =
  let top, focused, bot = to_lists d in
  let a = List.fold_left (fun a -> flat (f a) false) a top in
  let a = List.fold_left (fun a -> flat (f a) true)  a focused in
  let a = List.fold_left (fun a -> flat (f a) false) a bot in
  a
