(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open CErrors
open Names
open Values
open Constr

(** This module defines the representation of values internally used by
the native compiler *)

type ('a,'b) eq = ('a,'b) Util.eq = Refl : ('a,'a) eq

type t
let t_eq : (t, t -> t) eq = Obj.magic ()
let t_eq2 : (t, t -> t -> t) eq = Obj.magic ()
let t_eq3 : (t, t -> t -> t -> t) eq = Obj.magic ()
let t_eq4 : (t, t -> t -> t -> t -> t) eq = Obj.magic ()

let cast_gen (type a) (type b) (e:(a,b) eq) (x:a) : b =
  let Refl = e in x

let apply (f:t) : t -> t =
  cast_gen t_eq f

(* Writing this as [apply2 f x y = apply (apply f x) y] seems to
   confuse ocaml and it produces less efficient code.

   When written with a direct [cast_gen t_eq2] ocaml seems smart
   enough to fully reduce it where used. *)
let apply2 (f:t) : t -> t -> t =
  cast_gen t_eq2 f

let apply3 (f:t) : t -> t -> t -> t =
  cast_gen t_eq3 f

let apply4 (f:t) : t -> t -> t -> t -> t =
  cast_gen t_eq4 f

let of_fun (f:t->t) : t =
  cast_gen (sym t_eq) f

let eta_expand f = of_fun (fun x -> apply f x)

type accumulator (* = t (* a block [0:code;atom;arguments] *) *)

type tag = int

type arity = int

type reloc_table = (tag * arity) array

type annot_sw = {
    asw_ind : inductive;
    asw_reloc : reloc_table;
    asw_finite : bool;
    asw_prefix : string
  }

(* We compare only what is relevant for generation of ml code *)
let eq_annot_sw asw1 asw2 =
  Ind.CanOrd.equal asw1.asw_ind asw2.asw_ind &&
  String.equal asw1.asw_prefix asw2.asw_prefix

open Hashset.Combine

let hash_annot_sw asw =
  combine (Ind.CanOrd.hash asw.asw_ind) (String.hash asw.asw_prefix)

type sort_annot = string * int

type rec_pos = int array

let eq_rec_pos = Array.equal Int.equal

type vcofix = CofixLazy of t | CofixValue of t

type atom =
  | Arel of int
  | Aconstant of pconstant
  | Aind of pinductive
  | Asort of Sorts.t
  | Avar of Id.t
  | Acase of annot_sw * accumulator * t * t
  | Afix of t array * t array * rec_pos * int
            (* types, bodies, rec_pos, pos *)
  | Acofix of t array * t array * int * vcofix
  | Aevar of Evar.t * t array
  | Aproj of (inductive * int) * accumulator

type symbol =
  | SymbValue of t
  | SymbSort of Sorts.t
  | SymbName of Name.t
  | SymbConst of Constant.t
  | SymbMatch of annot_sw
  | SymbInd of inductive
  | SymbEvar of Evar.t
  | SymbInstance of UVars.Instance.t
  | SymbProj of (inductive * int)

type block

type symbols = symbol array

let empty_symbols = [| |]


let accumulate_tag = 0

(** Unique pointer used to drive the accumulator function *)
let ret_accu = Obj.repr (ref ())

type accu_val = { mutable acc_atm : atom; acc_arg : t list }

external set_tag : Obj.t -> int -> unit = "rocq_obj_set_tag"

let mk_accu (a : atom) : t =
  let rec accumulate data x =
    if Obj.repr x == ret_accu then Obj.repr data
    else
      let data = { data with acc_arg = x :: data.acc_arg } in
      let ans = Obj.repr (accumulate data) in
      let () = set_tag ans accumulate_tag in
      ans
  in
  let acc = { acc_atm = a; acc_arg = [] } in
  let ans = Obj.repr (accumulate acc) in
  (** FIXME: use another representation for accumulators, this causes naked
      pointers. *)
  let () = set_tag ans accumulate_tag in
  (Obj.obj ans : t)

let get_accu (k : accumulator) =
  (Obj.magic k : Obj.t -> accu_val) ret_accu

let mk_rel_accu i =
  mk_accu (Arel i)

let rel_tbl_size = 100
let rel_tbl_init = ref false
(* Initialize the table lazily not to generate naked pointers at startup *)
let rel_tbl = Array.make rel_tbl_size (Obj.magic 0 : t)

let mk_rel_accu i =
  if i < rel_tbl_size then
    let () =
      if not !rel_tbl_init then begin
        for i = 0 to rel_tbl_size - 1 do
          rel_tbl.(i) <- mk_rel_accu i
        done;
        rel_tbl_init := true
      end
    in
    rel_tbl.(i)
  else mk_rel_accu i

let mk_rels_accu lvl len =
  Array.init len (fun i -> mk_rel_accu (lvl + i))

let napply (f:t) (args: t array) =
  Array.fold_left (fun f a -> apply f a) f args

let mk_constant_accu kn u = mk_accu (Aconstant (kn,u))

let mk_ind_accu ind u = mk_accu (Aind (ind,u))

let mk_sort_accu s u =
  let s = UVars.subst_instance_sort u s in
  mk_accu (Asort s)

let mk_var_accu id =
  mk_accu (Avar id)

let mk_sw_accu annot c p ac =
  mk_accu (Acase(annot,c,p,ac))

let prod_tag =
  (* We rely on the tag of Vprod! *)
  let () = assert (Obj.tag (Obj.repr (Vprod (Anonymous, Obj.magic 0, Obj.magic 0))) == 2) in
  2

let mk_prod s dom codom =
  (* [Prod (s, dom, codom)] is coded as [tag:0|[tag:2|s; dom; codom]]
     This looks like a PArray but has a tag distinct from all PArray values on
     the inner block. This cannot be an accumulator because all accumulators
     have length >= 2. *)
  let block = Obj.repr (Vprod (s, dom, codom)) in
  (Obj.magic (ref block) : t)

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
  (get_accu k).acc_arg

let mk_fix_accu rec_pos pos types bodies =
  mk_accu (Afix(types,bodies,rec_pos, pos))

let mk_cofix_accu pos types norm =
  mk_accu (Acofix (types, norm, pos, CofixLazy (Obj.magic 0 : t)))

let upd_cofix (cofix :t) (cofix_fun : t) =
  let atom = atom_of_accu (Obj.magic cofix) in
  match atom with
  | Acofix (typ,norm,pos,_) ->
    set_atom_of_accu (Obj.magic cofix) (Acofix (typ, norm, pos, CofixLazy cofix_fun))
  | _ -> assert false

let force_cofix (cofix : t) =
  let accu = (Obj.magic cofix : accumulator) in
  let atom = atom_of_accu accu in
  match atom with
  | Acofix (typ, norm, pos, CofixLazy f) ->
    let args = args_of_accu accu in
    let f = List.fold_right (fun arg f -> apply f arg) args f in
    let v = apply f (Obj.magic ()) in
    let () = set_atom_of_accu accu (Acofix (typ, norm, pos, CofixValue v)) in
      v
  | Acofix (_, _, _, CofixValue v) -> v
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
  fun () -> of_fun (fun _ -> anomaly ~label:"native" (Pp.str "Evaluation failed."))

let cast_accu v = (Obj.magic v:accumulator)
[@@ocaml.inline always]

let mk_int (x : int) = (Obj.magic x : t)
[@@ocaml.inline always]

(* Rocq's booleans are reversed... *)
let mk_bool (b : bool) = (Obj.magic (not b) : t)
[@@ocaml.inline always]

let mk_uint (x : Uint63.t) = (Obj.magic x : t)
[@@ocaml.inline always]

let mk_float (x : Float64.t) = (Obj.magic x : t)
[@@ocaml.inline always]

let mk_string (x : Pstring.t) = (Obj.magic x : t)
[@@ocaml.inline always]

let block_size (b:block) =
  Obj.size (Obj.magic b)

let block_field (b:block) i = (Obj.magic (Obj.field (Obj.magic b) i) : t)

let block_tag (b:block) =
  Obj.tag (Obj.magic b)

type kind = (t, accumulator, t -> t, Name.t * t * t, Empty.t, Empty.t, block) Values.kind

let kind_of_value (v:t) =
  let o = Obj.repr v in
  if Obj.is_int o then Vconst (Obj.magic v)
  else
    let tag = Obj.tag o in
    if Int.equal tag accumulate_tag then
      if Int.equal (Obj.size o) 1 then
        let w = Obj.field o 0 in
        let tag = Obj.tag w in
        if Int.equal tag prod_tag then Obj.magic w
        else Varray (Obj.magic v)
      else Vaccu (Obj.magic v)
    else if Int.equal tag Obj.custom_tag then Vint64 (Obj.magic v)
    else if Int.equal tag Obj.double_tag then Vfloat64 (Obj.magic v)
    else if Int.equal tag Obj.string_tag then Vstring (Obj.magic v)
    else if (tag < Obj.lazy_tag) then Vblock (Obj.magic v)
      else
        (* assert (tag = Obj.closure_tag || tag = Obj.infix_tag);
           or ??? what is 1002*)
        Vfun (apply v)

(** Support for machine integers *)

let is_int (x:t) =
  let o = Obj.repr x in
  Obj.is_int o || Int.equal (Obj.tag o) Obj.custom_tag
[@@ocaml.inline always]

let val_to_int (x:t) = (Obj.magic x : int)
[@@ocaml.inline always]

let to_uint (x:t) = (Obj.magic x : Uint63.t)
[@@ocaml.inline always]

let no_check_head0 x =
 mk_uint (Uint63.head0 (to_uint x))
[@@ocaml.inline always]

let head0 accu x =
 if is_int x then  no_check_head0 x
 else apply accu x

let no_check_tail0 x =
  mk_uint (Uint63.tail0 (to_uint x))
[@@ocaml.inline always]

let tail0 accu x =
 if is_int x then no_check_tail0 x
 else apply accu x

let no_check_add  x y =
  mk_uint (Uint63.add (to_uint x) (to_uint y))
[@@ocaml.inline always]

let add accu x y =
  if is_int x && is_int y then no_check_add x y
  else apply2 accu x y

let no_check_sub x y =
  mk_uint (Uint63.sub (to_uint x) (to_uint y))
[@@ocaml.inline always]

let sub accu x y =
  if is_int x && is_int y then no_check_sub x y
  else apply2 accu x y

let no_check_mul x y =
  mk_uint (Uint63.mul (to_uint x) (to_uint y))
[@@ocaml.inline always]

let mul accu x y =
  if is_int x && is_int y then no_check_mul x y
  else apply2 accu x y

let no_check_div x y =
  mk_uint (Uint63.div (to_uint x) (to_uint y))
[@@ocaml.inline always]

let div accu x y =
  if is_int x && is_int y then no_check_div x y
  else apply2 accu x y

let no_check_rem x y =
  mk_uint (Uint63.rem (to_uint x) (to_uint y))
[@@ocaml.inline always]

let rem accu x y =
  if is_int x && is_int y then no_check_rem x y
  else apply2 accu x y

let no_check_divs x y =
  mk_uint (Uint63.divs (to_uint x) (to_uint y))
[@@ocaml.inline always]

let divs accu x y =
  if is_int x && is_int y then no_check_divs x y
  else apply2 accu x y

let no_check_rems x y =
  mk_uint (Uint63.rems (to_uint x) (to_uint y))
[@@ocaml.inline always]

let rems accu x y =
  if is_int x && is_int y then no_check_rems x y
  else apply2 accu x y

let no_check_l_sr x y =
  mk_uint (Uint63.l_sr (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_sr accu x y =
  if is_int x && is_int y then no_check_l_sr x y
  else apply2 accu x y

let no_check_l_sl x y =
  mk_uint (Uint63.l_sl (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_sl accu x y =
  if is_int x && is_int y then no_check_l_sl x y
  else apply2 accu x y

let no_check_a_sr x y =
  mk_uint (Uint63.a_sr (to_uint x) (to_uint y))
[@@ocaml.inline always]

let a_sr accu x y =
  if is_int x && is_int y then no_check_a_sr x y
  else apply2 accu x y

let no_check_l_and x y =
  mk_uint (Uint63.l_and (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_and accu x y =
  if is_int x && is_int y then no_check_l_and x y
  else apply2 accu x y

let no_check_l_xor x y =
  mk_uint (Uint63.l_xor (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_xor accu x y =
  if is_int x && is_int y then no_check_l_xor x y
  else apply2 accu x y

let no_check_l_or x y =
  mk_uint (Uint63.l_or (to_uint x) (to_uint y))
[@@ocaml.inline always]

let l_or accu x y =
  if is_int x && is_int y then no_check_l_or x y
  else apply2 accu x y

[@@@ocaml.warning "-37"]
type rocq_carry =
  | Caccu of t
  | C0 of t
  | C1 of t

type rocq_pair =
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
  else apply2 accu x y

let no_check_subc x y =
  let s = Uint63.sub (to_uint x) (to_uint y) in
  mkCarry (Uint63.lt (to_uint x) (to_uint y)) s
[@@ocaml.inline always]

let subc accu x y =
  if is_int x && is_int y then no_check_subc x y
  else apply2 accu x y

let no_check_addCarryC x y =
  let s =
    Uint63.add (Uint63.add (to_uint x) (to_uint y))
      (Uint63.of_int 1) in
  mkCarry (Uint63.le s (to_uint x)) s
[@@ocaml.inline always]

let addCarryC accu x y =
  if is_int x && is_int y then no_check_addCarryC x y
  else apply2 accu x y

let no_check_subCarryC x y =
  let s =
    Uint63.sub (Uint63.sub (to_uint x) (to_uint y))
      (Uint63.of_int 1) in
  mkCarry (Uint63.le (to_uint x) (to_uint y)) s
[@@ocaml.inline always]

let subCarryC accu x y =
  if is_int x && is_int y then no_check_subCarryC x y
  else apply2 accu x y

let of_pair (x, y) =
  (Obj.magic (PPair(mk_uint x, mk_uint y)):t)
[@@ocaml.inline always]

let no_check_mulc x y =
  of_pair (Uint63.mulc (to_uint x) (to_uint y))
[@@ocaml.inline always]

let mulc accu x y =
  if is_int x && is_int y then no_check_mulc x y
  else apply2 accu x y

let no_check_diveucl x y =
  let i1, i2 = to_uint x, to_uint y in
  of_pair(Uint63.div i1 i2, Uint63.rem i1 i2)
[@@ocaml.inline always]

let diveucl accu x y =
  if is_int x && is_int y then no_check_diveucl x y
  else apply2 accu x y

let no_check_div21 x y z =
  let i1, i2, i3 = to_uint x, to_uint y, to_uint z in
  of_pair (Uint63.div21 i1 i2 i3)
[@@ocaml.inline always]

let div21 accu x y z =
  if is_int x && is_int y && is_int z then no_check_div21 x y z
  else apply3 accu x y z

let no_check_addMulDiv x y z =
  let p, i, j = to_uint x, to_uint y, to_uint z in
  mk_uint (Uint63.addmuldiv p i j)
[@@ocaml.inline always]

let addMulDiv accu x y z =
  if is_int x && is_int y && is_int z then no_check_addMulDiv x y z
  else apply3 accu x y z

[@@@ocaml.warning "-34"]
type rocq_bool =
  | Baccu of t
  | Btrue
  | Bfalse

type rocq_cmp =
  | CmpAccu of t
  | CmpEq
  | CmpLt
  | CmpGt

let no_check_eq x y =
  mk_bool (Uint63.equal (to_uint x) (to_uint y))
[@@ocaml.inline always]

let eq accu x y =
  if is_int x && is_int y then no_check_eq x y
  else apply2 accu x y

let no_check_lt x y =
  mk_bool (Uint63.lt (to_uint x) (to_uint y))
[@@ocaml.inline always]

let lt accu x y =
  if is_int x && is_int y then no_check_lt x y
  else apply2 accu x y

let no_check_le x y =
  mk_bool (Uint63.le (to_uint x) (to_uint y))
[@@ocaml.inline always]

let le accu x y =
  if is_int x && is_int y then no_check_le x y
  else apply2 accu x y

let no_check_lts x y =
  mk_bool (Uint63.lts (to_uint x) (to_uint y))
[@@ocaml.inline always]

let lts accu x y =
  if is_int x && is_int y then no_check_lts x y
  else apply2 accu x y

let no_check_les x y =
  mk_bool (Uint63.les (to_uint x) (to_uint y))
[@@ocaml.inline always]

let les accu x y =
  if is_int x && is_int y then no_check_les x y
  else apply2 accu x y

let no_check_compare x y =
  match Uint63.compare (to_uint x) (to_uint y) with
  | x when x < 0 -> (Obj.magic CmpLt:t)
  | 0 -> (Obj.magic CmpEq:t)
  | _ -> (Obj.magic CmpGt:t)

let compare accu x y =
  if is_int x && is_int y then no_check_compare x y
  else apply2 accu x y

let no_check_compares x y =
  match Uint63.compares (to_uint x) (to_uint y) with
  | x when x < 0 -> (Obj.magic CmpLt:t)
  | 0 -> (Obj.magic CmpEq:t)
  | _ -> (Obj.magic CmpGt:t)

let compares accu x y =
  if is_int x && is_int y then no_check_compares x y
  else apply2 accu x y

let print x =
  Printf.fprintf stderr "%s" (Uint63.to_string (to_uint x));
  flush stderr;
  x

(** Support for machine floating point values *)

external is_float : t -> bool = "rocq_is_double"
[@@noalloc]

let to_float (x:t) = (Obj.magic x : Float64.t)
[@@ocaml.inline always]

let no_check_fopp x =
  mk_float (Float64.opp (to_float x))
[@@ocaml.inline always]

let fopp accu x =
  if is_float x then no_check_fopp x
  else apply accu x

let no_check_fabs x =
  mk_float (Float64.abs (to_float x))
[@@ocaml.inline always]

let fabs accu x =
  if is_float x then no_check_fabs x
  else apply accu x

let no_check_feq x y =
  mk_bool (Float64.eq (to_float x) (to_float y))
[@@ocaml.inline always]

let feq accu x y =
  if is_float x && is_float y then no_check_feq x y
  else apply2 accu x y

let no_check_flt x y =
  mk_bool (Float64.lt (to_float x) (to_float y))
[@@ocaml.inline always]

let flt accu x y =
  if is_float x && is_float y then no_check_flt x y
  else apply2 accu x y

let no_check_fle x y =
  mk_bool (Float64.le (to_float x) (to_float y))
[@@ocaml.inline always]

let fle accu x y =
  if is_float x && is_float y then no_check_fle x y
  else apply2 accu x y

type rocq_fcmp =
  | CFcmpAccu of t
  | CFcmpEq
  | CFcmpLt
  | CFcmpGt
  | CFcmpNotComparable

let no_check_fcompare x y =
  let c = Float64.compare (to_float x) (to_float y) in
  (Obj.magic c:t)
[@@ocaml.inline always]

let fcompare accu x y =
  if is_float x && is_float y then no_check_fcompare x y
  else apply2 accu x y

let no_check_fequal x y =
  mk_bool (Float64.equal (to_float x) (to_float y))
[@@ocaml.inline always]

let fequal accu x y =
  if is_float x && is_float y then no_check_fequal x y
  else apply2 accu x y

type rocq_fclass =
  | CFclassAccu of t
  | CFclassPNormal
  | CFclassNNormal
  | CFclassPSubn
  | CFclassNSubn
  | CFclassPZero
  | CFclassNZero
  | CFclassPInf
  | CFclassNInf
  | CFclassNaN

let no_check_fclassify x =
  let c = Float64.classify (to_float x) in
  (Obj.magic c:t)
[@@ocaml.inline always]

let fclassify accu x =
  if is_float x then no_check_fclassify x
  else apply accu x

let no_check_fadd x y =
  mk_float (Float64.add (to_float x) (to_float y))
[@@ocaml.inline always]

let fadd accu x y =
  if is_float x && is_float y then no_check_fadd x y
  else apply2 accu x y

let no_check_fsub x y =
  mk_float (Float64.sub (to_float x) (to_float y))
[@@ocaml.inline always]

let fsub accu x y =
  if is_float x && is_float y then no_check_fsub x y
  else apply2 accu x y

let no_check_fmul x y =
  mk_float (Float64.mul (to_float x) (to_float y))
[@@ocaml.inline always]

let fmul accu x y =
  if is_float x && is_float y then no_check_fmul x y
  else apply2 accu x y

let no_check_fdiv x y =
  mk_float (Float64.div (to_float x) (to_float y))
[@@ocaml.inline always]

let fdiv accu x y =
  if is_float x && is_float y then no_check_fdiv x y
  else apply2 accu x y

let no_check_fsqrt x =
  mk_float (Float64.sqrt (to_float x))
[@@ocaml.inline always]

let fsqrt accu x =
  if is_float x then no_check_fsqrt x
  else apply accu x

let no_check_float_of_int x =
  mk_float (Float64.of_uint63 (to_uint x))
[@@ocaml.inline always]

let float_of_int accu x =
  if is_int x then no_check_float_of_int x
  else apply accu x

let no_check_normfr_mantissa x =
  mk_uint (Float64.normfr_mantissa (to_float x))
[@@ocaml.inline always]

let normfr_mantissa accu x =
  if is_float x then no_check_normfr_mantissa x
  else apply accu x

let no_check_frshiftexp x =
  let f, e = Float64.frshiftexp (to_float x) in
  (Obj.magic (PPair(mk_float f, mk_uint e)):t)
[@@ocaml.inline always]

let frshiftexp accu x =
  if is_float x then no_check_frshiftexp x
  else apply accu x

let no_check_ldshiftexp x e =
  mk_float (Float64.ldshiftexp (to_float x) (to_uint e))
[@@ocaml.inline always]

let ldshiftexp accu x e =
  if is_float x && is_int e then no_check_ldshiftexp x e
  else apply2 accu x e

let no_check_next_up x =
  mk_float (Float64.next_up (to_float x))
[@@ocaml.inline always]

let next_up accu x =
  if is_float x then no_check_next_up x
  else apply accu x

let no_check_next_down x =
  mk_float (Float64.next_down (to_float x))
[@@ocaml.inline always]

let next_down accu x =
  if is_float x then no_check_next_down x
  else apply accu x

(** Support for primitive strings *)

let is_string (x:t) =
  let o = Obj.repr x in
  Int.equal (Obj.tag o) Obj.string_tag

let to_string (x:t) = (Obj.magic x : Pstring.t)
[@@ocaml.inline always]

let no_check_string_make n c =
  mk_string (Pstring.make (to_uint n) (to_uint c))
[@@ocaml.inline always]

let no_check_string_length s =
  mk_uint (Pstring.length (to_string s))
[@@ocaml.inline always]

let no_check_string_get s i =
  mk_uint (Pstring.get (to_string s) (to_uint i))
[@@ocaml.inline always]

let no_check_string_sub s off len =
  mk_string (Pstring.sub (to_string s) (to_uint off) (to_uint len))
[@@ocaml.inline always]

let no_check_string_cat s1 s2 =
  mk_string (Pstring.cat (to_string s1) (to_string s2))
[@@ocaml.inline always]

let no_check_string_compare s1 s2 =
  match Pstring.compare (to_string s1) (to_string s2) with
  | x when x < 0 -> (Obj.magic CmpLt:t)
  | 0 -> (Obj.magic CmpEq:t)
  | _ -> (Obj.magic CmpGt:t)

let string_make accu n c =
  if is_int n && is_int c then
    no_check_string_make n c
  else
    apply2 accu n c

let string_length accu s =
  if is_string s then
    no_check_string_length s
  else
    apply accu s

let string_get accu s i =
  if is_string s && is_int i then
    no_check_string_get s i
  else
    apply2 accu s i

let string_sub accu s off len =
  if is_string s && is_int off && is_int len then
    no_check_string_sub s off len
  else
    apply3 accu s off len

let string_cat accu s1 s2 =
  if is_string s1 && is_string s2 then
    no_check_string_cat s1 s2
  else
    apply2 accu s1 s2

let string_compare accu s1 s2 =
  if is_string s1 && is_string s2 then
    no_check_string_compare s1 s2
  else
    apply2 accu s1 s2

(** Support for primitive arrays *)

let is_parray t =
  (* This is only used over values known to inhabit an array type, so we just
     have to discriminate between actual arrays and accumulators. The latter
     are always closures with the tag set to 0, so they have size >= 2. *)
  let t = Obj.magic t in
  Obj.is_block t && Obj.size t = 1

let to_parray t = Obj.magic t
let of_parray t = Obj.magic t

let no_check_arraymake n def =
  of_parray (Parray.make (to_uint n) def)
[@@ocaml.inline always]

let arraymake accu vA n def =
  if is_int n then
    no_check_arraymake n def
  else apply3 accu vA n def

let no_check_arrayget t n =
   Parray.get (to_parray t) (to_uint n)
[@@ocaml.inline always]

let arrayget accu vA t n =
  if is_parray t && is_int n then
    no_check_arrayget t n
  else apply3 accu vA t n

let no_check_arraydefault t =
  Parray.default (to_parray t)
[@@ocaml.inline always]

let arraydefault accu vA t =
  if is_parray t then
    no_check_arraydefault t
  else apply2 accu vA t

let no_check_arrayset t n v =
  of_parray (Parray.set (to_parray t) (to_uint n) v)
[@@ocaml.inline always]

let arrayset accu vA t n v =
  if is_parray t && is_int n then
    no_check_arrayset t n v
  else apply4 accu vA t n v

let no_check_arraycopy t =
  of_parray (Parray.copy (to_parray t))
[@@ocaml.inline always]

let arraycopy accu vA t =
  if is_parray t then
    no_check_arraycopy t
  else apply2 accu vA t

let no_check_arraylength t =
  mk_uint (Parray.length (to_parray t))
[@@ocaml.inline always]

let arraylength accu vA t =
  if is_parray t then
    no_check_arraylength t
  else apply2 accu vA t

let parray_of_array t def =
  (Obj.magic (Parray.unsafe_of_obj (Obj.repr t) def) : t)

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
