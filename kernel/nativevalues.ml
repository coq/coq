(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open CErrors
open Names
open Constr

(** This module defines the representation of values internally used by
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

(* We compare only what is relevant for generation of ml code *)
let eq_annot_sw asw1 asw2 =
  eq_ind asw1.asw_ind asw2.asw_ind &&
  String.equal asw1.asw_prefix asw2.asw_prefix

open Hashset.Combine

let hash_annot_sw asw =
  combine (ind_hash asw.asw_ind) (String.hash asw.asw_prefix)

type sort_annot = string * int

type rec_pos = int array

let eq_rec_pos = Array.equal Int.equal

type atom = 
  | Arel of int
  | Aconstant of pconstant
  | Aind of pinductive
  | Asort of Sorts.t
  | Avar of Id.t
  | Acase of annot_sw * accumulator * t * (t -> t)
  | Afix of t array * t array * rec_pos * int
            (* types, bodies, rec_pos, pos *)
  | Acofix of t array * t array * int * t
  | Acofixe of t array * t array * int * t
  | Aprod of Name.t * t * (t -> t)
  | Ameta of metavariable * t
  | Aevar of Evar.t * t array
  | Aproj of (inductive * int) * accumulator

let accumulate_tag = 0

(** Unique pointer used to drive the accumulator function *)
let ret_accu = Obj.repr (ref ())

type accu_val = { mutable acc_atm : atom; acc_arg : Obj.t list }

let mk_accu (a : atom) : t =
  let rec accumulate data x =
    if x == ret_accu then Obj.repr data
    else
      let data = { data with acc_arg = x :: data.acc_arg } in
      let ans = Obj.repr (accumulate data) in
      let () = Obj.set_tag ans accumulate_tag in
      ans
  in
  let acc = { acc_atm = a; acc_arg = [] } in
  let ans = Obj.repr (accumulate acc) in
  (** FIXME: use another representation for accumulators, this causes naked
      pointers. *)
  let () = Obj.set_tag ans accumulate_tag in
  (Obj.obj ans : t)

let get_accu (k : accumulator) =
  (Obj.magic k : Obj.t -> accu_val) ret_accu

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

let mk_constant_accu kn u = 
  mk_accu (Aconstant (kn,Univ.Instance.of_array u))

let mk_ind_accu ind u = 
  mk_accu (Aind (ind,Univ.Instance.of_array u))

let mk_sort_accu s u =
  let open Sorts in
  match s with
  | Prop | Set -> mk_accu (Asort s)
  | Type s ->
     let u = Univ.Instance.of_array u in
     let s = Univ.subst_instance_universe u s in
     mk_accu (Asort (Type s))

let mk_var_accu id = 
  mk_accu (Avar id)

let mk_sw_accu annot c p ac = 
  mk_accu (Acase(annot,c,p,ac))

let mk_prod_accu s dom codom =
  mk_accu (Aprod (s,dom,codom))

let mk_meta_accu mv ty =
  mk_accu (Ameta (mv,ty))

let mk_evar_accu ev args =
  mk_accu (Aevar (ev, args))

let mk_proj_accu kn c = 
  mk_accu (Aproj (kn,c))

let atom_of_accu (k:accumulator) =
  (get_accu k).acc_atm

let set_atom_of_accu (k:accumulator) (a:atom) =
  (get_accu k).acc_atm <- a

let accu_nargs (k:accumulator) =
  List.length (get_accu k).acc_arg

let args_of_accu (k:accumulator) =
  let acc = (get_accu k).acc_arg in
  (Obj.magic (Array.of_list acc) : t array)

let mk_fix_accu rec_pos pos types bodies =
  mk_accu (Afix(types,bodies,rec_pos, pos))

let mk_cofix_accu pos types norm =
  mk_accu (Acofix(types,norm,pos,(Obj.magic 0 : t)))

let upd_cofix (cofix :t) (cofix_fun : t) =
  let atom = atom_of_accu (Obj.magic cofix) in
  match atom with
  | Acofix (typ,norm,pos,_) ->
      set_atom_of_accu (Obj.magic cofix) (Acofix(typ,norm,pos,cofix_fun))
  | _ -> assert false
  
let force_cofix (cofix : t) = 
  let accu = (Obj.magic cofix : accumulator) in
  let atom = atom_of_accu accu in
  match atom with
  | Acofix(typ,norm,pos,f) ->
    let args = args_of_accu accu in
    let f = Array.fold_right (fun arg f -> f arg) args f in
    let v = f (Obj.magic ()) in
    set_atom_of_accu accu (Acofixe(typ,norm,pos,v));
      v
  | Acofixe(_,_,_,v) -> v
  | _ -> cofix

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
  fun () _ -> anomaly ~label:"native" (Pp.str "Evaluation failed.")

let cast_accu v = (Obj.magic v:accumulator)
[@@ocaml.inline always]

let mk_int (x : int) = (Obj.magic x : t)
[@@ocaml.inline always]

(* Coq's booleans are reversed... *)
let mk_bool (b : bool) = (Obj.magic (not b) : t)
[@@ocaml.inline always]

let mk_uint (x : Uint63.t) = (Obj.magic x : t)
[@@ocaml.inline always]

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
  | Vint64 of int64
  | Vblock of block

let kind_of_value (v:t) =
  let o = Obj.repr v in
  if Obj.is_int o then Vconst (Obj.magic v)
  else
    let tag = Obj.tag o in
    if Int.equal tag accumulate_tag then
      Vaccu (Obj.magic v)
    else if Int.equal tag Obj.custom_tag then Vint64 (Obj.magic v)
    else if (tag < Obj.lazy_tag) then Vblock (Obj.magic v)
      else
        (* assert (tag = Obj.closure_tag || tag = Obj.infix_tag); 
           or ??? what is 1002*)
        Vfun v

(** Support for machine integers *)

let is_int (x:t) =
  let o = Obj.repr x in
  Obj.is_int o || Int.equal (Obj.tag o) Obj.custom_tag

let val_to_int (x:t) = (Obj.magic x : int)
[@@ocaml.inline always]

let to_uint (x:t) = (Obj.magic x : Uint63.t)
[@@ocaml.inline always]

let no_check_head0 x =
 mk_uint (Uint63.head0 (to_uint x))
[@@ocaml.inline always]

let head0 accu x =
 if is_int x then  no_check_head0 x
 else accu x

let no_check_tail0 x =
  mk_uint (Uint63.tail0 (to_uint x))
[@@ocaml.inline always]

let tail0 accu x =
 if is_int x then no_check_tail0 x
 else accu x

let no_check_add  x y =
  mk_uint (Uint63.add (to_uint x) (to_uint y))
[@@ocaml.inline always]

let add accu x y =
  if is_int x && is_int y then no_check_add x y 
  else accu x y

let no_check_sub x y =
  mk_uint (Uint63.sub (to_uint x) (to_uint y))
[@@ocaml.inline always]

let sub accu x y =
  if is_int x && is_int y then no_check_sub x y
  else accu x y

let no_check_mul x y =
  mk_uint (Uint63.mul (to_uint x) (to_uint y))
[@@ocaml.inline always]

let mul accu x y =
  if is_int x && is_int y then no_check_mul x y
  else accu x y

let no_check_div x y =
  mk_uint (Uint63.div (to_uint x) (to_uint y))
[@@ocaml.inline always]

let div accu x y =
  if is_int x && is_int y then no_check_div x y 
  else accu x y

let no_check_rem x y =
  mk_uint (Uint63.rem (to_uint x) (to_uint y))
[@@ocaml.inline always]

let rem accu x y =
  if is_int x && is_int y then no_check_rem x y
  else accu x y

let no_check_l_sr x y =
  mk_uint (Uint63.l_sr (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_sr accu x y =
  if is_int x && is_int y then no_check_l_sr x y
  else accu x y

let no_check_l_sl x y =
  mk_uint (Uint63.l_sl (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_sl accu x y =
  if is_int x && is_int y then no_check_l_sl x y
  else accu x y

let no_check_l_and x y =
  mk_uint (Uint63.l_and (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_and accu x y =
  if is_int x && is_int y then no_check_l_and x y
  else accu x y

let no_check_l_xor x y =
  mk_uint (Uint63.l_xor (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_xor accu x y =
  if is_int x && is_int y then no_check_l_xor x y
  else accu x y

let no_check_l_or x y =
  mk_uint (Uint63.l_or (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_or accu x y =
  if is_int x && is_int y then no_check_l_or x y
  else accu x y

[@@@ocaml.warning "-37"]
type coq_carry = 
  | Caccu of t
  | C0 of t
  | C1 of t

type coq_pair = 
  | Paccu of t
  | PPair of t * t

let mkCarry b i =
  if b then (Obj.magic (C1(mk_uint i)):t)
  else (Obj.magic (C0(mk_uint i)):t)

let no_check_addc x y =
  let s = Uint63.add (to_uint x) (to_uint y) in
  mkCarry (Uint63.lt s (to_uint x)) s
[@@ocaml.inline always]

let addc accu x y =
  if is_int x && is_int y then no_check_addc x y
  else accu x y

let no_check_subc x y =
  let s = Uint63.sub (to_uint x) (to_uint y) in
  mkCarry (Uint63.lt (to_uint x) (to_uint y)) s
[@@ocaml.inline always]

let subc accu x y =
  if is_int x && is_int y then no_check_subc x y
  else accu x y

let no_check_addCarryC x y =
  let s = 
    Uint63.add (Uint63.add (to_uint x) (to_uint y))
      (Uint63.of_int 1) in
  mkCarry (Uint63.le s (to_uint x)) s
[@@ocaml.inline always]

let addCarryC accu x y =
  if is_int x && is_int y then no_check_addCarryC x y
  else accu x y 

let no_check_subCarryC x y =
  let s = 
    Uint63.sub (Uint63.sub (to_uint x) (to_uint y))
      (Uint63.of_int 1) in
  mkCarry (Uint63.le (to_uint x) (to_uint y)) s
[@@ocaml.inline always]

let subCarryC accu x y =
  if is_int x && is_int y then no_check_subCarryC x y
  else accu x y 

let of_pair (x, y) =
  (Obj.magic (PPair(mk_uint x, mk_uint y)):t)
[@@ocaml.inline always]

let no_check_mulc x y =
  of_pair (Uint63.mulc (to_uint x) (to_uint y))
[@@ocaml.inline always]

let mulc accu x y =
  if is_int x && is_int y then no_check_mulc x y
  else accu x y

let no_check_diveucl x y =
  let i1, i2 = to_uint x, to_uint y in
  of_pair(Uint63.div i1 i2, Uint63.rem i1 i2)
[@@ocaml.inline always]

let diveucl accu x y =
  if is_int x && is_int y then no_check_diveucl x y
  else accu x y

let no_check_div21 x y z =
  let i1, i2, i3 = to_uint x, to_uint y, to_uint z in
  of_pair (Uint63.div21 i1 i2 i3)
[@@ocaml.inline always]

let div21 accu x y z =
  if is_int x && is_int y && is_int z then no_check_div21 x y z
  else accu x y z

let no_check_addMulDiv x y z =
  let p, i, j = to_uint x, to_uint y, to_uint z in
  mk_uint (Uint63.addmuldiv p i j)
[@@ocaml.inline always]

let addMulDiv accu x y z =
  if is_int x && is_int y && is_int z then no_check_addMulDiv x y z
  else accu x y z

[@@@ocaml.warning "-34"]
type coq_bool =
  | Baccu of t
  | Btrue
  | Bfalse

type coq_cmp =
  | CmpAccu of t
  | CmpEq 
  | CmpLt
  | CmpGt

let no_check_eq x y =
  mk_bool (Uint63.equal (to_uint x) (to_uint y))
[@@ocaml.inline always]

let eq accu x y =
  if is_int x && is_int y then no_check_eq x y
  else accu x y

let no_check_lt x y =
  mk_bool (Uint63.lt (to_uint x) (to_uint y))
[@@ocaml.inline always]

let lt accu x y =
  if is_int x && is_int y then no_check_lt x y
  else accu x y

let no_check_le x y =
  mk_bool (Uint63.le (to_uint x) (to_uint y))
[@@ocaml.inline always]

let le accu x y =
  if is_int x && is_int y then no_check_le x y
  else accu x y

let no_check_compare x y =
  match Uint63.compare (to_uint x) (to_uint y) with
  | x when x < 0 -> (Obj.magic CmpLt:t)
  | 0 -> (Obj.magic CmpEq:t)
  | _ -> (Obj.magic CmpGt:t)

let compare accu x y =
  if is_int x && is_int y then no_check_compare x y
  else accu x y

let print x =
  Printf.fprintf stderr "%s" (Uint63.to_string (to_uint x));
  flush stderr;
  x

let hobcnv = Array.init 256 (fun i -> Printf.sprintf "%02x" i)
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
  let buf = Bytes.create 2 in
  for i = 0 to mshl_expr_len - 1 do
    Bytes.blit_string s (2*i) buf 0 2;
    Buffer.add_char mshl_expr (bin_of_hex (Bytes.to_string buf))
  done;
  Marshal.from_bytes (Buffer.to_bytes mshl_expr) 0
