(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Genarg
open Geninterp
open Tac2expr
open Tac2interp

(** Dynamic tags *)

let val_tag t = match val_tag t with
| Val.Base t -> t
| _ -> assert false

let val_constr = val_tag (topwit Stdarg.wit_constr)
let val_ident = val_tag (topwit Stdarg.wit_ident)
let val_pattern = Val.create "ltac2:pattern"
let val_pp = Val.create "ltac2:pp"
let val_sort = Val.create "ltac2:sort"
let val_cast = Val.create "ltac2:cast"
let val_inductive = Val.create "ltac2:inductive"
let val_constant = Val.create "ltac2:constant"
let val_constructor = Val.create "ltac2:constructor"
let val_projection = Val.create "ltac2:projection"
let val_univ = Val.create "ltac2:universe"
let val_kont : (Exninfo.iexn -> valexpr Proofview.tactic) Val.typ =
  Val.create "ltac2:kont"

let extract_val (type a) (tag : a Val.typ) (Val.Dyn (tag', v)) : a =
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
  ValExt (Val.Dyn (tag, c))

let to_ext tag = function
| ValExt e -> extract_val tag e
| _ -> assert false

let of_constr c = of_ext val_constr c
let to_constr c = to_ext val_constr c

let of_ident c = of_ext val_ident c
let to_ident c = to_ext val_ident c

let of_pattern c = of_ext val_pattern c
let to_pattern c = to_ext val_pattern c

(** FIXME: handle backtrace in Ltac2 exceptions *)
let of_exn c = match fst c with
| LtacError (kn, c) -> ValOpn (kn, c)
| _ -> of_ext val_exn c

let to_exn c = match c with
| ValOpn (kn, c) -> (LtacError (kn, c), Exninfo.null)
| _ -> to_ext val_exn c

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
