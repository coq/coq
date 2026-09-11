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
open Tac2dyn
open Tac2val

type 'a repr = {
  r_of : 'a -> valexpr;
  r_to : valexpr -> 'a;
}

let repr_of r x = r.r_of x
let repr_to r x = r.r_to x

let make_repr r_of r_to = { r_of; r_to; }

let map_repr f g r = {
  r_of = (fun x -> r.r_of (g x));
  r_to = (fun x -> f (r.r_to x));
}

type ind_data = (Names.Ind.t * Declarations.mutual_inductive_body)
type binder = (Names.Name.t EConstr.binder_annot * EConstr.types)

module ModField = struct
  type t =
    | Ref of Names.GlobRef.t
    | Submodule of Names.ModPath.t
    | Rewrule
end

type local_env = {
  local_named : Environ.named_context_val;
  local_rel : Environ.rel_context_val;
}

type 'a judge = {
  env : local_env;
  term : EConstr.t;
  typ : 'a;
}

type termj = EConstr.types judge
type typej = EConstr.ESorts.t judge

(** Dynamic tags *)

let val_exn = Val.create "exn"
let val_exninfo = Val.create "exninfo"
let val_constr = Val.create "constr"
let val_ident = Val.create "ident"
let val_pattern = Val.create "pattern"
let val_preterm = Val.create "preterm"
let val_matching_context = Val.create "matching_context"
let val_pp = Val.create "pp"
let val_evar = Val.create "evar"
let val_sort = Val.create "sort"
let val_cast = Val.create "cast"
let val_inductive = Val.create "inductive"
let val_constant = Val.create "constant"
let val_constructor = Val.create "constructor"
let val_projection = Val.create "projection"
let val_qvar = Val.create "qvar"
let val_case = Val.create "case"
let val_binder = Val.create "binder"
let val_instance = Val.create "instance"
let val_free = Val.create "free"
let val_uint63 = Val.create "uint63"
let val_float = Val.create "float"
let val_pstring = Val.create "pstring"
let val_ind_data : (Names.Ind.t * Declarations.mutual_inductive_body) Val.tag = Val.create "ind_data"
let val_transparent_state : TransparentState.t Val.tag = Val.create "transparent_state"
let val_pretype_flags = Val.create "pretype_flags"
let val_expected_type = Val.create "expected_type"
let val_reduction = Val.create "reduction"
let val_rewstrategy = Val.create "rewstrategy"
let val_modpath = Val.create "modpath"
let val_module_field = Val.create "module_field"
let val_scheme_kind : string Val.tag = Val.create "scheme_kind"
let val_local_env = Val.create "local_env"
let val_termj = Val.create "termj"
let val_typej = Val.create "typej"

let extract_val (type a) (type b) (tag : a Val.tag) (tag' : b Val.tag) (v : b) : a =
match Val.eq tag tag' with
| None -> assert false
| Some Refl -> v

(** Exception *)

exception LtacError of Names.KerName.t * valexpr array

(** Conversion functions *)

let valexpr = {
  r_of = (fun obj -> obj);
  r_to = (fun obj -> obj);
}

let of_unit () = ValInt 0

let to_unit = function
| ValInt 0 -> ()
| _ -> assert false

let unit = {
  r_of = of_unit;
  r_to = to_unit;
}

let of_int n = ValInt n
let to_int = function
| ValInt n -> n
| _ -> assert false

let int = {
  r_of = of_int;
  r_to = to_int;
}

let of_bool b = if b then ValInt 0 else ValInt 1

let to_bool = function
| ValInt 0 -> true
| ValInt 1 -> false
| _ -> assert false

let bool = {
  r_of = of_bool;
  r_to = to_bool;
}

let of_char n = ValInt (Char.code n)
let to_char = function
| ValInt n -> Char.chr n
| _ -> assert false

let char = {
  r_of = of_char;
  r_to = to_char;
}

let of_bytes s = ValStr s
let to_bytes = function
| ValStr s -> s
| _ -> assert false

let bytes = {
  r_of = of_bytes;
  r_to = to_bytes;
}

let of_string s = of_bytes (Bytes.of_string s)
let to_string s = Bytes.to_string (to_bytes s)
let string = {
  r_of = of_string;
  r_to = to_string;
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
}

let of_closure cls = ValCls cls

let to_closure = Tac2val.to_closure

let closure = {
  r_of = of_closure;
  r_to = to_closure;
}

type ('a, 'b) fun1 = 'a -> 'b Proofview.tactic

let of_fun1 to_arg of_res f =
  of_closure (mk_closure arity_one (fun x ->
      Proofview.Monad.map of_res @@
      f (to_arg x)))

let to_fun1 of_arg to_res f x =
  Proofview.Monad.map to_res @@
  apply (to_closure f) [of_arg x]

let fun1 arg res = {
  r_of = of_fun1 arg.r_to res.r_of;
  r_to = to_fun1 arg.r_of res.r_to;
}

let thunk r = fun1 unit r

type ('a, 'b, 'c) fun2 = 'a -> 'b -> 'c Proofview.tactic

let of_fun2 to_arg1 to_arg2 of_res f =
  of_closure (mk_closure (arity_suc arity_one) (fun x y ->
      Proofview.Monad.map of_res @@
      f (to_arg1 x) (to_arg2 y)))

let to_fun2 of_arg1 of_arg2 to_res f x y =
  Proofview.Monad.map to_res @@
  apply (to_closure f) [of_arg1 x; of_arg2 y]

let fun2 arg1 arg2 res = {
  r_of = of_fun2 arg1.r_to arg2.r_to res.r_of;
  r_to = to_fun2 arg1.r_of arg2.r_of res.r_to;
}

type ('a, 'b, 'c, 'd) fun3 = 'a -> 'b -> 'c -> 'd Proofview.tactic

let of_fun3 to_arg1 to_arg2 to_arg3 of_res f =
  of_closure (mk_closure (arity_suc (arity_suc arity_one)) (fun x y z ->
      Proofview.Monad.map of_res @@
      f (to_arg1 x) (to_arg2 y) (to_arg3 z)))

let to_fun3 of_arg1 of_arg2 of_arg3 to_res f x y z =
  Proofview.Monad.map to_res @@
  apply (to_closure f) [of_arg1 x; of_arg2 y; of_arg3 z]

let fun3 arg1 arg2 arg3 res = {
  r_of = of_fun3 arg1.r_to arg2.r_to arg3.r_to res.r_of;
  r_to = to_fun3 arg1.r_of arg2.r_of arg3.r_of res.r_to;
}


let of_ext tag c =
  ValExt (tag, c)

let to_ext tag = function
| ValExt (tag', e) -> extract_val tag tag' e
| _ -> assert false

let repr_ext tag = {
  r_of = (fun e -> of_ext tag e);
  r_to = (fun e -> to_ext tag e);
}

let of_constr c = of_ext val_constr c
let to_constr c = to_ext val_constr c
let constr = repr_ext val_constr

let of_matching_context c = of_ext val_matching_context c
let to_matching_context c = to_ext val_matching_context c
let matching_context = repr_ext val_matching_context

let of_preterm c = of_ext val_preterm c
let to_preterm c = to_ext val_preterm c
let preterm = repr_ext val_preterm

let of_cast c = of_ext val_cast c
let to_cast c = to_ext val_cast c
let cast = repr_ext val_cast

let of_ident c = of_ext val_ident c
let to_ident c = to_ext val_ident c
let ident = repr_ext val_ident

let of_pattern c = of_ext val_pattern c
let to_pattern c = to_ext val_pattern c
let pattern = repr_ext val_pattern

let of_evar ev = of_ext val_evar ev
let to_evar ev = to_ext val_evar ev
let evar = repr_ext val_evar

let of_sort ev = of_ext val_sort ev
let to_sort ev = to_ext val_sort ev
let sort = repr_ext val_sort

let of_reduction ev = of_ext val_reduction ev
let to_reduction ev = to_ext val_reduction ev
let reduction = repr_ext val_reduction

let of_rewstrategy ev = of_ext val_rewstrategy ev
let to_rewstrategy ev = to_ext val_rewstrategy ev
let rewstrategy = repr_ext val_rewstrategy

let rocq_core n = Names.(KerName.make Tac2env.rocq_prefix (Id.of_string_soft n))

let internal_err = rocq_core "Internal"

let of_exninfo = of_ext val_exninfo
let to_exninfo = to_ext val_exninfo

let exninfo = {
  r_of = of_exninfo;
  r_to = to_exninfo;
}

(* Invariant: no [LtacError] should be put into a value with tag [val_exn]. *)
let of_err e = of_ext val_exn e
let to_err e = to_ext val_exn e
let err = repr_ext val_exn

(** FIXME: handle backtrace in Ltac2 exceptions *)
let of_exn c = match fst c with
| LtacError (kn, c) -> ValOpn (kn, c)
| _ -> ValOpn (internal_err, [|of_err c|])

let to_exn c = match c with
| ValOpn (kn, c) ->
  if Names.KerName.equal kn internal_err then
    to_err c.(0)
  else
    (LtacError (kn, c), Exninfo.null)
| _ -> assert false

let exn = {
  r_of = of_exn;
  r_to = to_exn;
}

let of_result of_ok = function
  | Ok v -> ValBlk (0, [|of_ok v|])
  | Error e -> ValBlk (1, [|of_exn e|])

let to_result to_ok = function
  | ValBlk (0, [|v|]) -> Ok (to_ok v)
  | ValBlk (1, [|e|]) -> Error (to_exn e)
  | _ -> assert false

let result ok = {
  r_of = of_result ok.r_of;
  r_to = to_result ok.r_to;
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
}

let of_triple f g h (x, y, z) = ValBlk (0, [|f x; g y; h z|])
let to_triple f g h = function
| ValBlk (0, [|x; y; z|]) -> (f x, g y, h z)
| _ -> assert false
let triple r0 r1 r2 = {
  r_of = (fun p -> of_triple r0.r_of r1.r_of r2.r_of p);
  r_to = (fun p -> to_triple r0.r_to r1.r_to r2.r_to p);
}

let of_array f vl = ValBlk (0, Array.map f vl)
let to_array f = function
| ValBlk (0, vl) -> Array.map f vl
| _ -> assert false
let array r = {
  r_of = (fun l -> of_array r.r_of l);
  r_to = (fun l -> to_array r.r_to l);
}

let of_block (n, args) = ValBlk (n, args)
let to_block = function
| ValBlk (n, args) -> (n, args)
| _ -> assert false

let block = {
  r_of = of_block;
  r_to = to_block;
}

let of_open (kn, args) = ValOpn (kn, args)

let to_open = function
| ValOpn (kn, args) -> (kn, args)
| _ -> assert false

let open_ = {
  r_of = of_open;
  r_to = to_open;
}

let of_free n = of_ext val_free n
let to_free x = to_ext val_free x

let free = {
  r_of = of_free;
  r_to = to_free;
}

let of_uint63 n = of_ext val_uint63 n
let to_uint63 x = to_ext val_uint63 x

let uint63 = {
  r_of = of_uint63;
  r_to = to_uint63;
}

let of_float f = of_ext val_float f
let to_float x = to_ext val_float x

let float = {
  r_of = of_float;
  r_to = to_float;
}

let of_pstring s = of_ext val_pstring s
let to_pstring x = to_ext val_pstring x

let pstring = {
  r_of = of_pstring;
  r_to = to_pstring;
}

let of_transparent_state c = of_ext val_transparent_state c
let to_transparent_state c = to_ext val_transparent_state c
let transparent_state = repr_ext val_transparent_state

let of_pretype_flags c = of_ext val_pretype_flags c
let to_pretype_flags c = to_ext val_pretype_flags c
let pretype_flags = repr_ext val_pretype_flags

let of_expected_type c = of_ext val_expected_type c
let to_expected_type c = to_ext val_expected_type c
let expected_type = repr_ext val_expected_type

let of_ind_data c = of_ext val_ind_data c
let to_ind_data c = to_ext val_ind_data c
let ind_data = repr_ext val_ind_data

let of_inductive c = of_ext val_inductive c
let to_inductive c = to_ext val_inductive c
let inductive = repr_ext val_inductive

let of_constant c = of_ext val_constant c
let to_constant c = to_ext val_constant c
let constant = repr_ext val_constant

let of_constructor c = of_ext val_constructor c
let to_constructor c = to_ext val_constructor c
let constructor = repr_ext val_constructor

let of_projection c = of_ext val_projection c
let to_projection c = to_ext val_projection c
let projection = repr_ext val_projection

let of_qvar c = of_ext val_qvar c
let to_qvar c = to_ext val_qvar c
let qvar = repr_ext val_qvar

let of_case c = of_ext val_case c
let to_case c = to_ext val_case c
let case = repr_ext val_case

let of_binder c = of_ext val_binder c
let to_binder c = to_ext val_binder c
let binder = repr_ext val_binder

let of_instance c = of_ext val_instance c
let to_instance c = to_ext val_instance c
let instance = repr_ext val_instance

let of_modpath c = of_ext val_modpath c
let to_modpath c = to_ext val_modpath c
let modpath = repr_ext val_modpath

let of_scheme_kind c = of_ext val_scheme_kind c
let to_scheme_kind c = to_ext val_scheme_kind c
let scheme_kind = repr_ext val_scheme_kind

let of_module_field c = of_ext val_module_field c
let to_module_field c = to_ext val_module_field c
let module_field = repr_ext val_module_field

let of_local_env = of_ext val_local_env
let to_local_env = to_ext val_local_env
let local_env = repr_ext val_local_env

let of_termj = of_ext val_termj
let to_termj = to_ext val_termj
let termj = repr_ext val_termj

let of_typej = of_ext val_typej
let to_typej = to_ext val_typej
let typej = repr_ext val_typej

let of_reference = let open Names.GlobRef in function
| VarRef id -> ValBlk (0, [| of_ident id |])
| ConstRef cst -> ValBlk (1, [| of_constant cst |])
| IndRef ind -> ValBlk (2, [| of_inductive ind |])
| ConstructRef cstr -> ValBlk (3, [| of_constructor cstr |])

let to_reference = let open Names.GlobRef in function
| ValBlk (0, [| id |]) -> VarRef (to_ident id)
| ValBlk (1, [| cst |]) -> ConstRef (to_constant cst)
| ValBlk (2, [| ind |]) -> IndRef (to_inductive ind)
| ValBlk (3, [| cstr |]) -> ConstructRef (to_constructor cstr)
| _ -> assert false

let reference = {
  r_of = of_reference;
  r_to = to_reference;
}

let of_strategy_level = let open Conv_oracle in function
| Expand -> ValInt 0
| Opaque -> ValInt 1
| Level n -> ValBlk (0, [| of_int n |])

let to_strategy_level = let open Conv_oracle in function
| ValInt 0 -> Expand
| ValInt 1 -> Opaque
| ValBlk (0, [| n |]) -> Level (to_int n)
| _ -> assert false

let strategy_level = {
  r_of = of_strategy_level;
  r_to = to_strategy_level;
}

let of_relevance = function
  | Sorts.Relevant -> ValInt 0
  | Sorts.Irrelevant -> ValInt 1
  | Sorts.RelevanceVar q -> ValBlk (0, [|of_qvar q|])

let to_relevance = function
  | ValInt 0 -> Sorts.Relevant
  | ValInt 1 -> Sorts.Irrelevant
  | ValBlk (0, [|qvar|]) ->
    let qvar = to_qvar qvar in
    Sorts.RelevanceVar qvar
  | _ -> assert false

(* XXX ltac2 exposes relevance internals so breaks ERelevance abstraction
   ltac2 Constr.Binder.relevance probably needs to be made an abstract type *)
let relevance = make_repr of_relevance to_relevance

let err_notfocussed =
  LtacError (rocq_core "Not_focussed", [||])

let err_outofbounds =
  LtacError (rocq_core "Out_of_bounds", [||])

let err_notfound =
  LtacError (rocq_core "Not_found", [||])

let err_matchfailure =
  LtacError (rocq_core "Match_failure", [||])

let err_division_by_zero =
  LtacError (rocq_core "Division_by_zero", [||])

let err_invalid_arg msg = LtacError (rocq_core "Invalid_argument", [|of_option of_pp msg|])
