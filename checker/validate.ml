(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

type error_context = string list
let mt_ec : error_context = []
let (/) (ctx:error_context) s : error_context = s::ctx
let overr (ctx:error_context) f = (fun (_:error_context) -> f ctx) 
let ext s f (ctx:error_context) = f (ctx/s)


exception ValidObjError of string * error_context * Obj.t
let fail ctx o s = raise (ValidObjError(s,ctx,o))

type func = error_context -> Obj.t -> unit

let apply debug f x =
  let o = Obj.repr x in
  try f mt_ec o
  with ValidObjError(msg,ctx,obj) ->
    if debug then begin
      print_endline ("Validation failed: "^msg);
      print_endline ("Context: "^String.concat"/"(List.rev ctx));
      pr_obj obj
    end;
    failwith "vo structure validation failed"

(* data not validated *)
let no_val (c:error_context) (o:Obj.t) = ()

(* Check that object o is a block with tag t *)
let val_tag t ctx o =
  if Obj.is_block o && Obj.tag o = t then ()
  else fail ctx o ("expected tag "^string_of_int t)

let val_block ctx o =
  if Obj.is_block o then
    (if Obj.tag o > Obj.no_scan_tag then
      fail ctx o "block: found no scan tag")
  else fail ctx o "expected block obj"

(* Check that an object is a tuple (or a record). v is an array of
   validation functions for each field. Its size corresponds to the
   expected size of the object. *)
let val_tuple ?name v ctx o =
  let ctx = match name with
      Some n -> ctx/n
    | _ -> ctx in
  let n = Array.length v in
  let val_fld i f =
    f (ctx/("fld="^string_of_int i)) (Obj.field o i) in
  val_block ctx o;
  if Obj.size o = n then Array.iteri val_fld v
  else
    fail ctx o
      ("tuple size: found "^string_of_int (Obj.size o)^
	 ", expected "^string_of_int n)

(* Check that the object is either a constant constructor of tag < cc,
   or a constructed variant. each element of vv is an array of
   validation functions to be applied to the constructor arguments.
   The size of vv corresponds to the number of non-constant
   constructors, and the size of vv.(i) is the expected arity of the
   i-th non-constant constructor. *)
let val_sum name cc vv ctx o =
  let ctx = ctx/name in
  if Obj.is_block o then
    (val_block (ctx/name) o;
    let n = Array.length vv in
    let i = Obj.tag o in
    let ctx' = if n=1 then ctx else ctx/("tag="^string_of_int i) in
    if i < n then val_tuple vv.(i) ctx' o
    else fail ctx' o ("sum: unexpected tag"))
  else if Obj.is_int o then
    let (n:int) = Obj.magic o in
    (if n<0 || n>=cc then
      fail ctx o ("bad constant constructor "^string_of_int n))
  else fail ctx o "not a sum"

let val_enum s n = val_sum s n [||]

(* Recursive types: avoid looping by eta-expansion *)
let rec val_rec_sum name cc f ctx o =
  val_sum name cc (f (overr (ctx/name) (val_rec_sum name cc f))) ctx o

(**************************************************************************)
(* Builtin types *)

(* Check the o is an array of values satisfying f. *)
let val_array ?(pos=false) f ctx o =
  let upd_ctx =
    if pos then (fun i -> ctx/string_of_int i) else (fun _ -> ctx) in
  val_block (ctx/"array") o;
  for i = 0 to Obj.size o - 1 do
    (f (upd_ctx i) (Obj.field o i):unit)
  done

(* Integer validator *)
let val_int ctx o =
  if not (Obj.is_int o) then fail ctx o "expected an int"

(* String validator *)
let val_str ctx o =
  try val_tag Obj.string_tag ctx o
  with Failure _ -> fail ctx o "expected a string"

(* Booleans *)
let val_bool = val_enum "bool" 2

(* Option type *)
let val_opt ?(name="option") f =
  val_sum name 1 [|[|f|]|]

(* Lists *)
let val_list ?(name="list") f ctx =
  val_rec_sum name 1 (fun vlist -> [|[|ext "elem" f;vlist|]|])
    ctx

(* Reference *)
let val_ref ?(name="ref") f ctx =
  val_tuple [|f|] (ctx/name)

(**************************************************************************)
(* Standard library types *)

(* Sets *)
let val_set ?(name="Set.t") f =
  val_rec_sum name 1
    (fun vset -> [|[|vset;ext "elem" f;
		     vset;ext "bal" val_int|]|])

(* Maps *)
let rec val_map ?(name="Map.t") fk fv =
  val_rec_sum name 1
    (fun vmap ->
       [|[|vmap; ext "key" fk; ext "value" fv;
	   vmap; ext "bal" val_int|]|])

(**************************************************************************)
(* Coq types *)

(* names *)
let val_id = val_str

let val_dp = val_list ~name:"dirpath" val_id

let val_name = val_sum "name" 1 [|[|val_id|]|]

let val_uid = val_tuple ~name:"uniq_ident" [|val_int;val_str;val_dp|]

let val_mp =
  val_rec_sum "module_path" 0
    (fun vmp -> [|[|val_dp|];[|val_uid|];[|vmp;val_id|]|])

let val_kn = val_tuple ~name:"kernel_name" [|val_mp;val_dp;val_id|]

let val_con =
  val_tuple ~name:"constant/mutind" [|val_kn;val_kn|]

let val_ind = val_tuple ~name:"inductive"[|val_con;val_int|]
let val_cstr = val_tuple ~name:"constructor"[|val_ind;val_int|]

(* univ *)
let val_level = val_sum "level" 1 [|[|val_dp;val_int|]|]
let val_univ = val_sum "univ" 0
  [|[|val_level|];[|val_list val_level;val_list val_level|]|]

let val_cstrs =
  val_set ~name:"Univ.constraints"
   (val_tuple ~name:"univ_constraint"
     [|val_level;val_enum "order_request" 3;val_level|])
