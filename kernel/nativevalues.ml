(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Term
open Names
open CErrors
open Util

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
  | Asort of sorts
  | Avar of identifier
  | Acase of annot_sw * accumulator * t * (t -> t)
  | Afix of t array * t array * rec_pos * int
            (* types, bodies, rec_pos, pos *)
  | Acofix of t array * t array * int * t
  | Acofixe of t array * t array * int * t
  | Aprod of name * t * (t -> t)
  | Ameta of metavariable * t
  | Aevar of existential * t
  | Aproj of constant * accumulator

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

let mk_constant_accu kn u = 
  mk_accu (Aconstant (kn,Univ.Instance.of_array u))

let mk_ind_accu ind u = 
  mk_accu (Aind (ind,Univ.Instance.of_array u))

let mk_sort_accu s u =
  match s with
  | Prop _ -> mk_accu (Asort s)
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

let mk_evar_accu ev ty =
  mk_accu (Aevar (ev,ty))

let mk_proj_accu kn c = 
  mk_accu (Aproj (kn,c))

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
  Obj.is_block o && Int.equal (Obj.tag o) accumulate_tag

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

let mk_int (x : int) = (Obj.magic x : t)
(* Coq's booleans are reversed... *)
let mk_bool (b : bool) = (Obj.magic (not b) : t)
let mk_uint (x : Uint31.t) = (Obj.magic x : t)

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
    if Int.equal tag accumulate_tag then
      Vaccu (Obj.magic v)
    else 
      if (tag < Obj.lazy_tag) then Vblock (Obj.magic v)
      else
        (* assert (tag = Obj.closure_tag || tag = Obj.infix_tag); 
           or ??? what is 1002*)
        Vfun v

(** Support for machine integers *)

let is_int (x:t) =
  let o = Obj.repr x in
  Obj.is_int o

let val_to_int (x:t) = (Obj.magic x : int)

let to_uint (x:t) = (Obj.magic x : Uint31.t)
let of_uint (x: Uint31.t) = (Obj.magic x : t)

let no_check_head0 x =
 of_uint (Uint31.head0 (to_uint x))

let head0 accu x =
 if is_int x then  no_check_head0 x
 else accu x

let no_check_tail0 x =
  of_uint (Uint31.tail0 (to_uint x))

let tail0 accu x =
 if is_int x then no_check_tail0 x
 else accu x

let no_check_add  x y =
  of_uint (Uint31.add (to_uint x) (to_uint y))

let add accu x y =
  if is_int x && is_int y then no_check_add x y 
  else accu x y

let no_check_sub x y =
     of_uint (Uint31.sub (to_uint x) (to_uint y))

let sub accu x y =
  if is_int x && is_int y then no_check_sub x y
  else accu x y

let no_check_mul x y =
  of_uint (Uint31.mul (to_uint x) (to_uint y))

let mul accu x y =
  if is_int x && is_int y then no_check_mul x y
  else accu x y

let no_check_div x y =
  of_uint (Uint31.div (to_uint x) (to_uint y))

let div accu x y =
  if is_int x && is_int y then no_check_div x y 
  else accu x y

let no_check_rem x y =
  of_uint (Uint31.rem (to_uint x) (to_uint y))

let rem accu x y =
  if is_int x && is_int y then no_check_rem x y
  else accu x y

let no_check_l_sr x y =
  of_uint (Uint31.l_sr (to_uint x) (to_uint y))

let l_sr accu x y =
  if is_int x && is_int y then no_check_l_sr x y
  else accu x y

let no_check_l_sl x y =
  of_uint (Uint31.l_sl (to_uint x) (to_uint y))

let l_sl accu x y =
  if is_int x && is_int y then no_check_l_sl x y
  else accu x y

let no_check_l_and x y =
  of_uint (Uint31.l_and (to_uint x) (to_uint y))

let l_and accu x y =
  if is_int x && is_int y then no_check_l_and x y
  else accu x y

let no_check_l_xor x y =
  of_uint (Uint31.l_xor (to_uint x) (to_uint y))

let l_xor accu x y =
  if is_int x && is_int y then no_check_l_xor x y
  else accu x y

let no_check_l_or x y =
  of_uint (Uint31.l_or (to_uint x) (to_uint y))

let l_or accu x y =
  if is_int x && is_int y then no_check_l_or x y
  else accu x y

type coq_carry = 
  | Caccu of t
  | C0 of t
  | C1 of t

type coq_pair = 
  | Paccu of t
  | PPair of t * t

type coq_zn2z =
  | Zaccu of t
  | ZW0
  | ZWW of t * t

let mkCarry b i =
  if b then (Obj.magic (C1(of_uint i)):t)
  else (Obj.magic (C0(of_uint i)):t)

let no_check_addc x y =
  let s = Uint31.add (to_uint x) (to_uint y) in
  mkCarry (Uint31.lt s (to_uint x)) s

let addc accu x y =
  if is_int x && is_int y then no_check_addc x y
  else accu x y

let no_check_subc x y =
  let s = Uint31.sub (to_uint x) (to_uint y) in
  mkCarry (Uint31.lt (to_uint x) (to_uint y)) s

let subc accu x y =
  if is_int x && is_int y then no_check_subc x y
  else accu x y

let no_check_addcarryc x y =
  let s = 
    Uint31.add (Uint31.add (to_uint x) (to_uint y))
      (Uint31.of_int 1) in
  mkCarry (Uint31.le s (to_uint x)) s

let addcarryc accu x y =
  if is_int x && is_int y then no_check_addcarryc x y
  else accu x y 

let no_check_subcarryc x y =
  let s = 
    Uint31.sub (Uint31.sub (to_uint x) (to_uint y))
      (Uint31.of_int 1) in
  mkCarry (Uint31.le (to_uint x) (to_uint y)) s

let subcarryc accu x y =
  if is_int x && is_int y then no_check_subcarryc x y
  else accu x y 

let of_pair (x, y) =
  (Obj.magic (PPair(of_uint x, of_uint y)):t)

let zn2z_of_pair (x,y) =
  if Uint31.equal x (Uint31.of_uint 0) &&
    Uint31.equal y (Uint31.of_uint 0) then Obj.magic ZW0
  else (Obj.magic (ZWW(of_uint x, of_uint y)) : t)

let no_check_mulc x y =
  zn2z_of_pair(Uint31.mulc (to_uint x) (to_uint y))

let mulc accu x y =
  if is_int x && is_int y then no_check_mulc x y
  else accu x y

let no_check_diveucl x y =
  let i1, i2 = to_uint x, to_uint y in
  of_pair(Uint31.div i1 i2, Uint31.rem i1 i2)

let diveucl accu x y =
  if is_int x && is_int y then no_check_diveucl x y
  else accu x y

let no_check_div21 x y z =
  let i1, i2, i3 = to_uint x, to_uint y, to_uint z in
  of_pair (Uint31.div21 i1 i2 i3)

let div21 accu x y z =
  if is_int x && is_int y && is_int z then no_check_div21 x y z
  else accu x y z

let no_check_addmuldiv x y z =
  let p, i, j = to_uint x, to_uint y, to_uint z in
  let p' = Uint31.to_int p in
  of_uint (Uint31.l_or 
	     (Uint31.l_sl i p) 
	     (Uint31.l_sr j (Uint31.of_int (31 - p'))))

let addmuldiv accu x y z =
  if is_int x && is_int y && is_int z then no_check_addmuldiv x y z
  else accu x y z


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
  mk_bool (Uint31.equal (to_uint x) (to_uint y))

let eq accu x y =
  if is_int x && is_int y then no_check_eq x y
  else accu x y

let no_check_lt x y =
  mk_bool (Uint31.lt (to_uint x) (to_uint y))

let lt accu x y =
  if is_int x && is_int y then no_check_lt x y
  else accu x y

let no_check_le x y =
  mk_bool (Uint31.le (to_uint x) (to_uint y))

let le accu x y =
  if is_int x && is_int y then no_check_le x y
  else accu x y

let no_check_compare x y =
  match Uint31.compare (to_uint x) (to_uint y) with
  | x when x < 0 -> (Obj.magic CmpLt:t)
  | 0 -> (Obj.magic CmpEq:t)
  | _ -> (Obj.magic CmpGt:t)

let compare accu x y =
  if is_int x && is_int y then no_check_compare x y
  else accu x y

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
  let buf = String.create 2 in
  for i = 0 to mshl_expr_len - 1 do
    String.blit s (2*i) buf 0 2;
    Buffer.add_char mshl_expr (bin_of_hex buf)
  done;
  Marshal.from_string (Buffer.contents mshl_expr) 0

(** Retroknowledge, to be removed when we switch to primitive integers *)

(* This will be unsafe with 63-bits integers *)
let digit_to_uint d = (Obj.magic d : Uint31.t)

let mk_I31_accu c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
		  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 =
  if is_int x0 && is_int x1 && is_int x2 && is_int x3 && is_int x4 && is_int x5
     && is_int x6 && is_int x7 && is_int x8 && is_int x9 && is_int x10
     && is_int x11 && is_int x12 && is_int x13 && is_int x14 && is_int x15
     && is_int x16 && is_int x17 && is_int x18 && is_int x19 && is_int x20
     && is_int x21 && is_int x22 && is_int x23 && is_int x24 && is_int x25
     && is_int x26 && is_int x27 && is_int x28 && is_int x29 && is_int x30
  then
    let r = digit_to_uint x0 in
    let r = Uint31.add_digit r (digit_to_uint x1) in
    let r = Uint31.add_digit r (digit_to_uint x2) in
    let r = Uint31.add_digit r (digit_to_uint x3) in
    let r = Uint31.add_digit r (digit_to_uint x4) in
    let r = Uint31.add_digit r (digit_to_uint x5) in
    let r = Uint31.add_digit r (digit_to_uint x6) in
    let r = Uint31.add_digit r (digit_to_uint x7) in
    let r = Uint31.add_digit r (digit_to_uint x8) in
    let r = Uint31.add_digit r (digit_to_uint x9) in
    let r = Uint31.add_digit r (digit_to_uint x10) in
    let r = Uint31.add_digit r (digit_to_uint x11) in
    let r = Uint31.add_digit r (digit_to_uint x12) in
    let r = Uint31.add_digit r (digit_to_uint x13) in
    let r = Uint31.add_digit r (digit_to_uint x14) in
    let r = Uint31.add_digit r (digit_to_uint x15) in
    let r = Uint31.add_digit r (digit_to_uint x16) in
    let r = Uint31.add_digit r (digit_to_uint x17) in
    let r = Uint31.add_digit r (digit_to_uint x18) in
    let r = Uint31.add_digit r (digit_to_uint x19) in
    let r = Uint31.add_digit r (digit_to_uint x20) in
    let r = Uint31.add_digit r (digit_to_uint x21) in
    let r = Uint31.add_digit r (digit_to_uint x22) in
    let r = Uint31.add_digit r (digit_to_uint x23) in
    let r = Uint31.add_digit r (digit_to_uint x24) in
    let r = Uint31.add_digit r (digit_to_uint x25) in
    let r = Uint31.add_digit r (digit_to_uint x26) in
    let r = Uint31.add_digit r (digit_to_uint x27) in
    let r = Uint31.add_digit r (digit_to_uint x28) in
    let r = Uint31.add_digit r (digit_to_uint x29) in
    let r = Uint31.add_digit r (digit_to_uint x30) in
    mk_uint r
  else
    c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30

let decomp_uint c v =
  if is_int v then
    let r = ref c in
    let v = val_to_int v in
    for i = 30 downto 0 do
      r := (!r) (mk_int ((v lsr i) land 1));
    done;
    !r
  else v
