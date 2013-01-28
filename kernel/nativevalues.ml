(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Term
open Names
open Errors

(** This modules defines the representation of values internally used by
the native compiler *)

type t = t -> t
    
type accumulator (* = t (* a block [0:code;atom;arguments] *) *)

type tag = int
 
type arity = int

type reloc_table = (tag * arity) array

type annot_sw = {
    asw_ind : inductive;
    asw_ci : case_info;
    asw_reloc : reloc_table;
    asw_finite : bool;
    asw_prefix : string
  }

type sort_annot = string * int

type rec_pos = int array

type atom = 
  | Arel of int
  | Aconstant of constant
  | Aind of inductive
  | Asort of sorts
  | Avar of identifier
  | Acase of annot_sw * accumulator * t * (t -> t)
  | Afix of  t array * t array * rec_pos * int
  | Acofix of t array * t array * int * t
  | Acofixe of t array * t array * int * t
  | Aprod of name * t * (t -> t)

let accumulate_tag = 0

let accumulate_code (k:accumulator) (x:t) =
  let o = Obj.repr k in
  let osize = Obj.size o in
  let r = Obj.new_block accumulate_tag (osize + 1) in
  for i = 0 to osize - 1 do
    Obj.set_field r i (Obj.field o i)
  done;
  Obj.set_field r osize (Obj.repr x);
  (Obj.obj r:t)

let rec accumulate (x:t) =
  accumulate_code (Obj.magic accumulate) x

let raccumulate = ref accumulate

let mk_accu_gen rcode (a:atom) =
(*  Format.eprintf "size rcode =%i\n" (Obj.size (Obj.magic rcode)); *)
  let r = Obj.new_block 0 3 in
  Obj.set_field r 0 (Obj.field (Obj.magic rcode) 0);
  Obj.set_field r 1 (Obj.field (Obj.magic rcode) 1);
  Obj.set_field r 2 (Obj.magic a);
  (Obj.magic r:t);;

let mk_accu (a:atom) = mk_accu_gen accumulate a

let mk_rel_accu i = 
  mk_accu (Arel i)

let rel_tbl_size = 100 
let rel_tbl = Array.init rel_tbl_size mk_rel_accu

let mk_rel_accu i = 
  if i < rel_tbl_size then rel_tbl.(i)
  else mk_rel_accu i

let mk_rels_accu lvl len =
  Array.init len (fun i -> mk_rel_accu (lvl + i))

let napply (f:t) (args: t array) =
  Array.fold_left (fun f a -> f a) f args

let mk_constant_accu kn = 
  mk_accu (Aconstant kn)

let mk_ind_accu s = 
  mk_accu (Aind s)

let mk_sort_accu s =
  mk_accu (Asort s)

let mk_var_accu id = 
  mk_accu (Avar id)

let mk_sw_accu annot c p ac = 
  mk_accu (Acase(annot,c,p,ac))

let mk_prod_accu s dom codom =
  mk_accu (Aprod (s,dom,codom))

let atom_of_accu (k:accumulator) =
  (Obj.magic (Obj.field (Obj.magic k) 2) : atom)

let set_atom_of_accu (k:accumulator) (a:atom) =
  Obj.set_field (Obj.magic k) 2 (Obj.magic a)

let accu_nargs (k:accumulator) =
  let nargs = Obj.size (Obj.magic k) - 3 in
(*  if nargs < 0 then Format.eprintf "nargs = %i\n" nargs; *)
  assert (nargs >= 0);
  nargs

let args_of_accu (k:accumulator) =
  let nargs = accu_nargs k in
  let f i = (Obj.magic (Obj.field (Obj.magic k) (nargs-i+2)) : t) in
  let t = Array.init nargs f in
  Array.to_list t

let is_accu x =
  let o = Obj.repr x in
  Obj.is_block o && Obj.tag o = accumulate_tag

(*let accumulate_fix_code (k:accumulator) (a:t) =
  match atom_of_accu k with
  | Afix(frec,_,rec_pos,_,_) ->
      let nargs = accu_nargs k in
      if nargs <> rec_pos || is_accu a then
	accumulate_code k a
      else
        let r = ref frec in
        for i = 0 to nargs - 1 do
	  r := !r (arg_of_accu k i)
        done;
        !r a
  | _ -> assert false


let rec accumulate_fix (x:t) =
  accumulate_fix_code (Obj.magic accumulate_fix) x

let raccumulate_fix = ref accumulate_fix *)

let is_atom_fix (a:atom) =
  match a with
  | Afix _ -> true
  | _ -> false

let mk_fix_accu rec_pos pos types bodies =
  mk_accu_gen accumulate (Afix(types,bodies,rec_pos, pos))

let mk_cofix_accu pos types norm =
  mk_accu_gen accumulate (Acofix(types,norm,pos,(Obj.magic 0 : t)))

let upd_cofix (cofix :t) (cofix_fun : t) =
  let atom = atom_of_accu (Obj.magic cofix) in
  match atom with
  | Acofix (typ,norm,pos,_) ->
      set_atom_of_accu (Obj.magic cofix) (Acofix(typ,norm,pos,cofix_fun))
  | _ -> assert false
  
let force_cofix (cofix : t) = 
  if is_accu cofix then
    let accu = (Obj.magic cofix : accumulator) in
    let atom = atom_of_accu accu in
    match atom with
    | Acofix(typ,norm,pos,f) ->
	let f = ref f in
    let args = List.rev (args_of_accu accu) in
    List.iter (fun x -> f := !f x) args;
	let v = !f (Obj.magic ()) in
	set_atom_of_accu accu (Acofixe(typ,norm,pos,v));
	v
    | Acofixe(_,_,_,v) -> v 
    | _ -> cofix
  else cofix

let mk_const tag = Obj.magic tag

let mk_block tag args =
  let nargs = Array.length args in
  let r = Obj.new_block tag nargs in
  for i = 0 to nargs - 1 do
    Obj.set_field r i (Obj.magic args.(i))
  done;
  (Obj.magic r : t)

(* Two instances of dummy_value should not be pointer equal, otherwise
 comparing them as terms would succeed *)
let dummy_value : unit -> t =
  fun () _ -> anomaly ~label:"native" (Pp.str "Evaluation failed")

let cast_accu v = (Obj.magic v:accumulator)

let mk_int x = Obj.magic x

type block

let block_size (b:block) =
  Obj.size (Obj.magic b)

let block_field (b:block) i = (Obj.magic (Obj.field (Obj.magic b) i) : t)

let block_tag (b:block) = 
  Obj.tag (Obj.magic b)

type kind_of_value =
  | Vaccu of accumulator
  | Vfun of (t -> t)
  | Vconst of int
  | Vblock of block
	
let kind_of_value (v:t) =
  let o = Obj.repr v in
  if Obj.is_int o then Vconst (Obj.magic v)
  else
    let tag = Obj.tag o in
    if tag = accumulate_tag then 
      Vaccu (Obj.magic v)
    else 
      if (tag < Obj.lazy_tag) then Vblock (Obj.magic v)
      else
        (* assert (tag = Obj.closure_tag || tag = Obj.infix_tag); 
           or ??? what is 1002*)
        Vfun v

let hobcnv = Array.init 256 (fun i -> Printf.sprintf "%.2x" i)
let bohcnv = Array.init 256 (fun i -> i -
                                      (if 0x30 <= i then 0x30 else 0) -
                                      (if 0x41 <= i then 0x7 else 0) -
                                      (if 0x61 <= i then 0x20 else 0))

let hex_of_bin ch = hobcnv.(int_of_char ch)
let bin_of_hex s = char_of_int (bohcnv.(int_of_char s.[0]) * 16 + bohcnv.(int_of_char s.[1]))

let str_encode expr =
  let mshl_expr = Marshal.to_string expr [] in
  let payload = Buffer.create (String.length mshl_expr * 2) in
  String.iter (fun c -> Buffer.add_string payload (hex_of_bin c)) mshl_expr;
  Buffer.contents payload

let str_decode s =
  let mshl_expr_len = String.length s / 2 in
  let mshl_expr = Buffer.create mshl_expr_len in
  let buf = String.create 2 in
  for i = 0 to mshl_expr_len - 1 do
    String.blit s (2*i) buf 0 2;
    Buffer.add_char mshl_expr (bin_of_hex buf)
  done;
  Marshal.from_string (Buffer.contents mshl_expr) 0


