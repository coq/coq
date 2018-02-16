(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module defines validation functions to ensure an imported
   value (using input_value) has the correct structure. *)

let rec pr_obj_rec o =
  if Obj.is_int o then
    Format.print_int(Obj.magic o)
  else if Obj.is_block o then
    let t = Obj.tag o in
    if t > Obj.no_scan_tag then
      if t = Obj.string_tag then
        Format.print_string ("\""^String.escaped(Obj.magic o)^"\"")
      else
        Format.print_string "?"
    else
      (let n = Obj.size o in
      Format.print_string ("#"^string_of_int t^"(");
      Format.open_hvbox 0;
      for i = 0 to n-1 do
        pr_obj_rec (Obj.field o i);
        if i<>n-1 then (Format.print_string ","; Format.print_cut())
      done;
      Format.close_box();
      Format.print_string ")")
  else Format.print_string "?"

let pr_obj o = pr_obj_rec o; Format.print_newline()

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

exception ValidObjError of string * error_context * Obj.t
let fail ctx o s = raise (ValidObjError(s,ctx,o))

(* Check that object o is a block with tag t *)
let val_tag t ctx o =
  if Obj.is_block o && Obj.tag o = t then ()
  else fail ctx o ("expected tag "^string_of_int t)

let val_block ctx o =
  if Obj.is_block o then
    (if Obj.tag o > Obj.no_scan_tag then
      fail ctx o "block: found no scan tag")
  else fail ctx o "expected block obj"

let val_dyn ctx o =
  let fail () = fail ctx o "expected a Dyn.t" in
  if not (Obj.is_block o) then fail ()
  else if not (Obj.size o = 2) then fail ()
  else if not (Obj.tag (Obj.field o 0) = Obj.int_tag) then fail ()
  else ()

open Values

let rec val_gen v ctx o = match v with
  | Tuple (name,vs) -> val_tuple ~name vs ctx o
  | Sum (name,cc,vv) -> val_sum name cc vv ctx o
  | Array v -> val_array v ctx o
  | List v0 -> val_sum "list" 1 [|[|Annot ("elem",v0);v|]|] ctx o
  | Opt v -> val_sum "option" 1 [|[|v|]|] ctx o
  | Int -> if not (Obj.is_int o) then fail ctx o "expected an int"
  | String ->
    (try val_tag Obj.string_tag ctx o
     with Failure _ -> fail ctx o "expected a string")
  | Any -> ()
  | Fail s -> fail ctx o ("unexpected object " ^ s)
  | Annot (s,v) -> val_gen v (ctx/CtxAnnot s) o
  | Dyn -> val_dyn ctx o
  | Proxy { contents = v } -> val_gen v ctx o
  | Uint63 -> val_uint63 ctx o

(* Check that an object is a tuple (or a record). vs is an array of
   value representation for each field. Its size corresponds to the
   expected size of the object. *)
and val_tuple ?name vs ctx o =
  let ctx = match name with
    | Some n -> ctx/CtxType n
    | _ -> ctx
  in
  let n = Array.length vs in
  let val_fld i v =
    val_gen v (ctx/(CtxField i)) (Obj.field o i) in
  val_block ctx o;
  if Obj.size o = n then Array.iteri val_fld vs
  else
    fail ctx o
      ("tuple size: found "^string_of_int (Obj.size o)^
	  ", expected "^string_of_int n)

(* Check that the object is either a constant constructor of tag < cc,
   or a constructed variant. each element of vv is an array of
   value representations of the constructor arguments.
   The size of vv corresponds to the number of non-constant
   constructors, and the size of vv.(i) is the expected arity of the
   i-th non-constant constructor. *)
and val_sum name cc vv ctx o =
  let ctx = ctx/CtxType name in
  if Obj.is_block o then
    (val_block ctx o;
    let n = Array.length vv in
    let i = Obj.tag o in
    let ctx' = if n=1 then ctx else ctx/CtxTag i in
    if i < n then val_tuple vv.(i) ctx' o
    else fail ctx' o ("sum: unexpected tag"))
  else if Obj.is_int o then
    let (n:int) = Obj.magic o in
    (if n<0 || n>=cc then
      fail ctx o ("bad constant constructor "^string_of_int n))
  else fail ctx o "not a sum"

(* Check the o is an array of values satisfying f. *)
and val_array v ctx o =
  val_block (ctx/CtxType "array") o;
  for i = 0 to Obj.size o - 1 do
    val_gen v ctx (Obj.field o i)
  done

and val_uint63 ctx o =
  if not (Uint63.is_uint63 o) then
    fail ctx o "not a 63-bit unsigned integer"

let print_frame = function
| CtxType t -> t
| CtxAnnot t -> t
| CtxField i -> Printf.sprintf "fld=%i" i
| CtxTag i -> Printf.sprintf "tag=%i" i

let validate debug v x =
  let o = Obj.repr x in
  try val_gen v mt_ec o
  with ValidObjError(msg,ctx,obj) ->
    (if debug then
      let ctx = List.rev_map print_frame ctx in
      print_endline ("Context: "^String.concat"/"ctx);
      pr_obj obj);
    failwith ("Validation failed: "^msg^" (in "^(print_frame (List.hd ctx))^")")
