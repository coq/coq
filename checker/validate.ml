(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Analyze

(* This module defines validation functions to ensure an imported
   value (using input_value) has the correct structure. *)

let rec pr_obj_rec mem o = match o with
| Int i ->
    Format.print_int i
| Ptr p ->
  let v = LargeArray.get mem p in
  begin match v with
  | Struct (tag, data) ->
    let n = Array.length data in
    Format.print_string ("#"^string_of_int tag^"(");
    Format.open_hvbox 0;
    for i = 0 to n-1 do
      pr_obj_rec mem (Array.get data i);
      if i<>n-1 then (Format.print_string ","; Format.print_cut())
    done;
    Format.close_box();
    Format.print_string ")"
  | String s ->
    Format.print_string ("\""^String.escaped s^"\"")
  | Int64 _
  | Float64 _ ->
    Format.print_string "?"
  end
| Atm tag ->
  Format.print_string ("#"^string_of_int tag^"()");
| Fun addr ->
  Format.printf "fun@%x" addr

let pr_obj mem o = pr_obj_rec mem o; Format.print_newline()

(**************************************************************************)
(* Obj low-level validators *)

type error_frame =
| CtxAnnot of string
| CtxType of string
| CtxField of int
| CtxTag of int

type error_context = error_frame list
let mt_ec : error_context = []
let (/) (ctx:error_context) s : error_context = s::ctx

exception ValidObjError of string * error_context * data
let fail _mem ctx o s = raise (ValidObjError(s,ctx,o))

let is_block mem o = match o with
| Ptr _ | Atm _ -> true
| Fun _ | Int _ -> false

let is_int _mem o = match o with
| Int _ -> true
| Fun _ | Ptr _ | Atm _ -> false

let is_int64 mem o = match o with
| Int _ | Fun _ | Atm _ -> false
| Ptr p ->
  match LargeArray.get mem p with
  | Int64 _ -> true
  | Float64 _ | Struct _ | String _ -> false

let is_float64 mem o = match o with
| Int _ | Fun _ | Atm _ -> false
| Ptr p ->
  match LargeArray.get mem p with
  | Float64 _ -> true
  | Int64 _ | Struct _ | String _ -> false

let get_int _mem = function
| Int i -> i
| Fun _ | Ptr _ | Atm _ -> assert false

let tag mem o = match o with
| Atm tag -> tag
| Fun _ -> Obj.out_of_heap_tag
| Int _ -> Obj.int_tag
| Ptr p ->
  match LargeArray.get mem p with
  | Struct (tag, _) -> tag
  | String _ -> Obj.string_tag
  | Float64 _ -> Obj.double_tag
  | Int64 _ -> Obj.custom_tag

let size mem o = match o with
| Atm _ -> 0
| Fun _ | Int _ -> assert false
| Ptr p ->
  match LargeArray.get mem p with
  | Struct (tag, blk) -> Array.length blk
  | String _ | Float64 _ | Int64 _ -> assert false

let field mem o i = match o with
| Atm _ | Fun _ | Int _ -> assert false
| Ptr p ->
  match LargeArray.get mem p with
  | Struct (tag, blk) -> Array.get blk i
  | String _ | Float64 _ | Int64 _ -> assert false

(* Check that object o is a block with tag t *)
let val_tag t mem ctx o =
  if is_block mem o && tag mem o = t then ()
  else fail mem ctx o ("expected tag "^string_of_int t)

let val_block mem ctx o =
  if is_block mem o then
    (if tag mem o > Obj.no_scan_tag then
      fail mem ctx o "block: found no scan tag")
  else fail mem ctx o "expected block obj"

open Values

type memory = {
  mem : obj LargeArray.t;
  seen : value list LargeArray.t;
}

let rec val_gen v mem ctx o = match o with
  | Ptr p ->
    let seen = LargeArray.get mem.seen p in
    if List.exists (fun v' -> Values.equal v' v) seen then ()
    else begin
      (* Setting before we recurse means we allow recursive values.
         Do we care? *)
      LargeArray.set mem.seen p (v::seen);
      val_gen_aux v mem ctx o
    end
  | Int _ | Atm _ | Fun _ -> val_gen_aux v mem ctx o

and val_gen_aux v mem ctx o = match kind v with
  | Tuple (name,vs) -> val_tuple ~name vs mem ctx o
  | Sum (name,cc,vv) -> val_sum name cc vv mem ctx o
  | Array v -> val_array v mem ctx o
  | List v0 -> val_sum "list" 1 [|[|v0;v|]|] mem ctx o
  | Opt v -> val_sum "option" 1 [|[|v|]|] mem ctx o
  | Int -> if not (is_int mem o) then fail mem ctx o "expected an int"
  | String ->
    (try val_tag Obj.string_tag mem.mem ctx o
     with Failure _ -> fail mem ctx o "expected a string")
  | Any -> ()
  | Fail s -> fail mem ctx o ("unexpected object " ^ s)
  | Annot (s,v) -> val_gen v mem (ctx/CtxAnnot s) o
  | Int64 -> val_int64 mem ctx o
  | Float64 -> val_float64 mem ctx o

(* Check that an object is a tuple (or a record). vs is an array of
   value representation for each field. Its size corresponds to the
   expected size of the object. *)
and val_tuple ?name vs mem ctx o =
  let ctx = match name with
    | Some n -> ctx/CtxType n
    | _ -> ctx
  in
  let n = Array.length vs in
  let val_fld i v =
    val_gen v mem (ctx/(CtxField i)) (field mem.mem o i) in
  val_block mem.mem ctx o;
  if size mem.mem o = n then Array.iteri val_fld vs
  else
    fail mem ctx o
      ("tuple size: found "^string_of_int (size mem.mem o)^
          ", expected "^string_of_int n)

(* Check that the object is either a constant constructor of tag < cc,
   or a constructed variant. each element of vv is an array of
   value representations of the constructor arguments.
   The size of vv corresponds to the number of non-constant
   constructors, and the size of vv.(i) is the expected arity of the
   i-th non-constant constructor. *)
and val_sum name cc vv mem ctx o =
  let ctx = ctx/CtxType name in
  if is_block mem o then
    (val_block mem.mem ctx o;
    let n = Array.length vv in
    let i = tag mem.mem o in
    let ctx' = if n=1 then ctx else ctx/CtxTag i in
    if i < n then val_tuple vv.(i) mem ctx' o
    else fail mem ctx' o ("sum: unexpected tag"))
  else if is_int mem o then
    let (n:int) = get_int mem o in
    (if n<0 || n>=cc then
      fail mem ctx o ("bad constant constructor "^string_of_int n))
  else fail mem ctx o "not a sum"

(* Check the o is an array of values satisfying f. *)
and val_array v mem ctx o =
  val_block mem.mem (ctx/CtxType "array") o;
  for i = 0 to size mem.mem o - 1 do
    val_gen v mem ctx (field mem.mem o i)
  done

and val_int64 mem ctx o =
  if not (is_int64 mem.mem o) then
    fail mem ctx o "not a 63-bit unsigned integer"

and val_float64 mem ctx o =
  if not (is_float64 mem.mem o) then
    fail mem ctx o "not a 64-bit float"

let val_gen v mem ctx o =
  let mem = {
    mem;
    seen = LargeArray.make (LargeArray.length mem) [];
  }
  in
  val_gen v mem ctx o

let print_frame = function
| CtxType t -> t
| CtxAnnot t -> t
| CtxField i -> Printf.sprintf "fld=%i" i
| CtxTag i -> Printf.sprintf "tag=%i" i

let validate v (o, mem) : unit =
  try NewProfile.profile "validate" (fun () -> val_gen v mem mt_ec o) ()
  with ValidObjError(msg,ctx,obj) ->
    let rctx = List.rev_map print_frame ctx in
    print_endline ("Context: "^String.concat"/"rctx);
    pr_obj mem obj;
    failwith ("Validation failed: "^msg^" (in "^(print_frame (List.hd ctx))^")")
