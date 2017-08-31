(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Globnames
open Genarg
open Tac2dyn
open Tac2expr
open Tac2interp

(** Dynamic tags *)

let val_exn = Val.create "exn"
let val_constr = Val.create "constr"
let val_ident = Val.create "ident"
let val_pattern = Val.create "pattern"
let val_pp = Val.create "pp"
let val_sort = Val.create "sort"
let val_cast = Val.create "cast"
let val_inductive = Val.create "inductive"
let val_constant = Val.create "constant"
let val_constructor = Val.create "constructor"
let val_projection = Val.create "projection"
let val_case = Val.create "case"
let val_univ = Val.create "universe"
let val_kont : (Exninfo.iexn -> valexpr Proofview.tactic) Val.tag =
  Val.create "kont"
let val_free : Names.Id.Set.t Val.tag = Val.create "free"

let extract_val (type a) (type b) (tag : a Val.tag) (tag' : b Val.tag) (v : b) : a =
match Val.eq tag tag' with
| None -> assert false
| Some Refl -> v

(** Conversion functions *)

let of_unit () = ValInt 0

let to_unit = function
| ValInt 0 -> ()
| _ -> assert false

let of_int n = ValInt n
let to_int = function
| ValInt n -> n
| _ -> assert false

let of_bool b = if b then ValInt 0 else ValInt 1

let to_bool = function
| ValInt 0 -> true
| ValInt 1 -> false
| _ -> assert false

let of_char n = ValInt (Char.code n)
let to_char = function
| ValInt n -> Char.chr n
| _ -> assert false

let of_string s = ValStr s
let to_string = function
| ValStr s -> s
| _ -> assert false

let rec of_list f = function
| [] -> ValInt 0
| x :: l -> ValBlk (0, [| f x; of_list f l |])

let rec to_list f = function
| ValInt 0 -> []
| ValBlk (0, [|v; vl|]) -> f v :: to_list f vl
| _ -> assert false

let of_ext tag c =
  ValExt (tag, c)

let to_ext tag = function
| ValExt (tag', e) -> extract_val tag tag' e
| _ -> assert false

let of_constr c = of_ext val_constr c
let to_constr c = to_ext val_constr c

let of_ident c = of_ext val_ident c
let to_ident c = to_ext val_ident c

let of_pattern c = of_ext val_pattern c
let to_pattern c = to_ext val_pattern c

let internal_err =
  let open Names in
  KerName.make2 Tac2env.coq_prefix (Label.of_id (Id.of_string "Internal"))

(** FIXME: handle backtrace in Ltac2 exceptions *)
let of_exn c = match fst c with
| LtacError (kn, c) -> ValOpn (kn, c)
| _ -> ValOpn (internal_err, [|of_ext val_exn c|])

let to_exn c = match c with
| ValOpn (kn, c) ->
  if Names.KerName.equal kn internal_err then
    to_ext val_exn c.(0)
  else
    (LtacError (kn, c), Exninfo.null)
| _ -> assert false

let of_option f = function
| None -> ValInt 0
| Some c -> ValBlk (0, [|f c|])

let to_option f = function
| ValInt 0 -> None
| ValBlk (0, [|c|]) -> Some (f c)
| _ -> assert false

let of_pp c = of_ext val_pp c
let to_pp c = to_ext val_pp c

let of_tuple cl = ValBlk (0, cl)
let to_tuple = function
| ValBlk (0, cl) -> cl
| _ -> assert false

let of_array f vl = ValBlk (0, Array.map f vl)
let to_array f = function
| ValBlk (0, vl) -> Array.map f vl
| _ -> assert false

let of_constant c = of_ext val_constant c
let to_constant c = to_ext val_constant c

let of_reference = function
| VarRef id -> ValBlk (0, [| of_ident id |])
| ConstRef cst -> ValBlk (1, [| of_constant cst |])
| IndRef ind -> ValBlk (2, [| of_ext val_inductive ind |])
| ConstructRef cstr -> ValBlk (3, [| of_ext val_constructor cstr |])

let to_reference = function
| ValBlk (0, [| id |]) -> VarRef (to_ident id)
| ValBlk (1, [| cst |]) -> ConstRef (to_constant cst)
| ValBlk (2, [| ind |]) -> IndRef (to_ext val_inductive ind)
| ValBlk (3, [| cstr |]) -> ConstructRef (to_ext val_constructor cstr)
| _ -> assert false
