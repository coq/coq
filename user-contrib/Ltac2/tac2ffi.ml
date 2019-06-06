(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Globnames
open Tac2dyn
open Tac2expr
open Proofview.Notations

type ('a, _) arity0 =
| OneAty : ('a, 'a -> 'a Proofview.tactic) arity0
| AddAty : ('a, 'b) arity0 -> ('a, 'a -> 'b) arity0

type valexpr =
| ValInt of int
  (** Immediate integers *)
| ValBlk of tag * valexpr array
  (** Structured blocks *)
| ValStr of Bytes.t
  (** Strings *)
| ValCls of closure
  (** Closures *)
| ValOpn of KerName.t * valexpr array
  (** Open constructors *)
| ValExt : 'a Tac2dyn.Val.tag * 'a -> valexpr
  (** Arbitrary data *)
| ValUint63 of Uint63.t
  (** Primitive integers *)

and closure = MLTactic : (valexpr, 'v) arity0 * 'v -> closure

let arity_one = OneAty
let arity_suc a = AddAty a

type 'a arity = (valexpr, 'a) arity0

let mk_closure arity f = MLTactic (arity, f)

module Valexpr =
struct

type t = valexpr

let is_int = function
| ValInt _ -> true
| ValBlk _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ | ValUint63 _ -> false

let tag v = match v with
| ValBlk (n, _) -> n
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ | ValUint63 _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let field v n = match v with
| ValBlk (_, v) -> v.(n)
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ | ValUint63 _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let set_field v n w = match v with
| ValBlk (_, v) -> v.(n) <- w
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ | ValUint63 _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let make_block tag v = ValBlk (tag, v)
let make_int n = ValInt n

end

type 'a repr = {
  r_of : 'a -> valexpr;
  r_to : valexpr -> 'a;
  r_id : bool;
}

let repr_of r x = r.r_of x
let repr_to r x = r.r_to x

let make_repr r_of r_to = { r_of; r_to; r_id = false; }

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
let val_free : Names.Id.Set.t Val.tag = Val.create "free"
let val_ltac1 : Geninterp.Val.t Val.tag = Val.create "ltac1"

let extract_val (type a) (type b) (tag : a Val.tag) (tag' : b Val.tag) (v : b) : a =
match Val.eq tag tag' with
| None -> assert false
| Some Refl -> v

(** Exception *)

exception LtacError of KerName.t * valexpr array

(** Conversion functions *)

let valexpr = {
  r_of = (fun obj -> obj);
  r_to = (fun obj -> obj);
  r_id = true;
}

let of_unit () = ValInt 0

let to_unit = function
| ValInt 0 -> ()
| _ -> assert false

let unit = {
  r_of = of_unit;
  r_to = to_unit;
  r_id = false;
}

let of_int n = ValInt n
let to_int = function
| ValInt n -> n
| _ -> assert false

let int = {
  r_of = of_int;
  r_to = to_int;
  r_id = false;
}

let of_bool b = if b then ValInt 0 else ValInt 1

let to_bool = function
| ValInt 0 -> true
| ValInt 1 -> false
| _ -> assert false

let bool = {
  r_of = of_bool;
  r_to = to_bool;
  r_id = false;
}

let of_char n = ValInt (Char.code n)
let to_char = function
| ValInt n -> Char.chr n
| _ -> assert false

let char = {
  r_of = of_char;
  r_to = to_char;
  r_id = false;
}

let of_string s = ValStr s
let to_string = function
| ValStr s -> s
| _ -> assert false

let string = {
  r_of = of_string;
  r_to = to_string;
  r_id = false;
}

let rec of_list f = function
| [] -> ValInt 0
| x :: l -> ValBlk (0, [| f x; of_list f l |])

let rec to_list f = function
| ValInt 0 -> []
| ValBlk (0, [|v; vl|]) -> f v :: to_list f vl
| _ -> assert false

let list r = {
  r_of = (fun l -> of_list r.r_of l);
  r_to = (fun l -> to_list r.r_to l);
  r_id = false;
}

let of_closure cls = ValCls cls

let to_closure = function
| ValCls cls -> cls
| ValExt _ | ValInt _ | ValBlk _ | ValStr _ | ValOpn _ | ValUint63 _ -> assert false

let closure = {
  r_of = of_closure;
  r_to = to_closure;
  r_id = false;
}

let of_ext tag c =
  ValExt (tag, c)

let to_ext tag = function
| ValExt (tag', e) -> extract_val tag tag' e
| _ -> assert false

let repr_ext tag = {
  r_of = (fun e -> of_ext tag e);
  r_to = (fun e -> to_ext tag e);
  r_id = false;
}

let of_constr c = of_ext val_constr c
let to_constr c = to_ext val_constr c
let constr = repr_ext val_constr

let of_ident c = of_ext val_ident c
let to_ident c = to_ext val_ident c
let ident = repr_ext val_ident

let of_pattern c = of_ext val_pattern c
let to_pattern c = to_ext val_pattern c
let pattern = repr_ext val_pattern

let internal_err =
  let open Names in
  let coq_prefix =
    MPfile (DirPath.make (List.map Id.of_string ["Init"; "Ltac2"]))
  in
  KerName.make coq_prefix (Label.of_id (Id.of_string "Internal"))

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

let exn = {
  r_of = of_exn;
  r_to = to_exn;
  r_id = false;
}

let of_option f = function
| None -> ValInt 0
| Some c -> ValBlk (0, [|f c|])

let to_option f = function
| ValInt 0 -> None
| ValBlk (0, [|c|]) -> Some (f c)
| _ -> assert false

let option r = {
  r_of = (fun l -> of_option r.r_of l);
  r_to = (fun l -> to_option r.r_to l);
  r_id = false;
}

let of_pp c = of_ext val_pp c
let to_pp c = to_ext val_pp c
let pp = repr_ext val_pp

let of_tuple cl = ValBlk (0, cl)
let to_tuple = function
| ValBlk (0, cl) -> cl
| _ -> assert false

let of_pair f g (x, y) = ValBlk (0, [|f x; g y|])
let to_pair f g = function
| ValBlk (0, [|x; y|]) -> (f x, g y)
| _ -> assert false
let pair r0 r1 = {
  r_of = (fun p -> of_pair r0.r_of r1.r_of p);
  r_to = (fun p -> to_pair r0.r_to r1.r_to p);
  r_id = false;
}

let of_array f vl = ValBlk (0, Array.map f vl)
let to_array f = function
| ValBlk (0, vl) -> Array.map f vl
| _ -> assert false
let array r = {
  r_of = (fun l -> of_array r.r_of l);
  r_to = (fun l -> to_array r.r_to l);
  r_id = false;
}

let of_block (n, args) = ValBlk (n, args)
let to_block = function
| ValBlk (n, args) -> (n, args)
| _ -> assert false

let block = {
  r_of = of_block;
  r_to = to_block;
  r_id = false;
}

let of_open (kn, args) = ValOpn (kn, args)

let to_open = function
| ValOpn (kn, args) -> (kn, args)
| _ -> assert false

let open_ = {
  r_of = of_open;
  r_to = to_open;
  r_id = false;
}

let of_uint63 n = ValUint63 n
let to_uint63 = function
| ValUint63 n -> n
| _ -> assert false

let uint63 = {
  r_of = of_uint63;
  r_to = to_uint63;
  r_id = false;
}

let of_constant c = of_ext val_constant c
let to_constant c = to_ext val_constant c
let constant = repr_ext val_constant

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

let reference = {
  r_of = of_reference;
  r_to = to_reference;
  r_id = false;
}

type ('a, 'b) fun1 = closure

let fun1 (r0 : 'a repr) (r1 : 'b repr) : ('a, 'b) fun1 repr = closure
let to_fun1 r0 r1 f = to_closure f

let rec apply : type a. a arity -> a -> valexpr list -> valexpr Proofview.tactic =
  fun arity f args -> match args, arity with
  | [], arity -> Proofview.tclUNIT (ValCls (MLTactic (arity, f)))
  (* A few hardcoded cases for efficiency *)
  | [a0], OneAty -> f a0
  | [a0; a1], AddAty OneAty -> f a0 a1
  | [a0; a1; a2], AddAty (AddAty OneAty) -> f a0 a1 a2
  | [a0; a1; a2; a3], AddAty (AddAty (AddAty OneAty)) -> f a0 a1 a2 a3
  (* Generic cases *)
  | a :: args, OneAty ->
    f a >>= fun f ->
    let MLTactic (arity, f) = to_closure f in
    apply arity f args
  | a :: args, AddAty arity ->
    apply arity (f a) args

let apply (MLTactic (arity, f)) args = apply arity f args

type n_closure =
| NClosure : 'a arity * (valexpr list -> 'a) -> n_closure

let rec abstract n f =
  if Int.equal n 1 then NClosure (OneAty, fun accu v -> f (List.rev (v :: accu)))
  else
    let NClosure (arity, fe) = abstract (n - 1) f in
    NClosure (AddAty arity, fun accu v -> fe (v :: accu))

let abstract n f =
  let () = assert (n > 0) in
  let NClosure (arity, f) = abstract n f in
  MLTactic (arity, f [])

let app_fun1 cls r0 r1 x =
  apply cls [r0.r_of x] >>= fun v -> Proofview.tclUNIT (r1.r_to v)
