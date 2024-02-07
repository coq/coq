(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
let val_univ = Val.create "universe"
let val_quality = Val.create "quality"
let val_free : Names.Id.Set.t Val.tag = Val.create "free"
let val_uint63 = Val.create "uint63"
let val_float = Val.create "float"
let val_ind_data : (Names.Ind.t * Declarations.mutual_inductive_body) Val.tag = Val.create "ind_data"
let val_transparent_state : TransparentState.t Val.tag = Val.create "transparent_state"
let val_pretype_flags = Val.create "pretype_flags"
let val_expected_type = Val.create "expected_type"

let extract_val (type a) (type b) (tag : a Val.tag) (tag' : b Val.tag) (v : b) : a =
match Val.eq tag tag' with
| None -> assert false
| Some Refl -> v

(** Exception *)

exception LtacError of Names.KerName.t * valexpr array

(** Type annotation *)

module Types = struct
  open Tac2expr

  type t = Any | Var of int | Ref of type_constant * t list | Tuple of t list | Arrow of t * t

  let any = Any

  let default t = Option.default Any t

  let var x = Var x

  let (!) x l = Ref (x, l)

  let (!!) x = ! x []

  let tuple l = Tuple l

  let (@->) x y = Arrow (x, y)

  let as_scheme t =
    let (!) x = x.contents in
    let var_cnt = ref 0 in
    (* find max explicit variable *)
    let rec iter = function
      | Any -> ()
      | Var x -> var_cnt := max !var_cnt (x+1)
      | Ref (_,l) | Tuple l -> List.iter iter l
      | Arrow (x,y) -> iter x; iter y
    in
    let () = iter t in
    (* assign each Any to different variables *)
    let rec as_ty = function
      | Any -> let x = !var_cnt in var_cnt := x+1; GTypVar x
      | Var x -> GTypVar x
      | Ref (kn, l) -> GTypRef (Other kn, List.map as_ty l)
      | Tuple l -> GTypRef (Tuple (List.length l), List.map as_ty l)
      | Arrow (x, y) -> GTypArrow (as_ty x, as_ty y)
    in
    let t = as_ty t in
    !var_cnt, t
end
open Types
module T = Tac2globals.Types

type 'a annotated = 'a * Types.t option

let typed x (ty:Types.t) = (x,Some ty)
let untyped x = (x,None)

(** Conversion functions *)

let valexpr = {
  r_of = (fun obj -> obj);
  r_to = (fun obj -> obj);
}

let valexpr_0 = typed valexpr (Types.var 0)

let of_unit () = ValInt 0

let to_unit = function
| ValInt 0 -> ()
| _ -> assert false

let unit_ = {
  r_of = of_unit;
  r_to = to_unit;
}

let unit = typed unit_ (!! T.unit)

let of_int n = ValInt n
let to_int = function
| ValInt n -> n
| _ -> assert false

let int_ = {
  r_of = of_int;
  r_to = to_int;
}

let int = typed int_ (!! T.int)

let of_bool b = if b then ValInt 0 else ValInt 1

let to_bool = function
| ValInt 0 -> true
| ValInt 1 -> false
| _ -> assert false

let bool_ = {
  r_of = of_bool;
  r_to = to_bool;
}

let bool = typed bool_ (!! T.bool)

let of_char n = ValInt (Char.code n)
let to_char = function
| ValInt n -> Char.chr n
| _ -> assert false

let char_ = {
  r_of = of_char;
  r_to = to_char;
}

let char = typed char_ (!! T.char)

let of_bytes s = ValStr s
let to_bytes = function
| ValStr s -> s
| _ -> assert false

let bytes_ = {
  r_of = of_bytes;
  r_to = to_bytes;
}

let bytes = typed bytes_ (!! T.string)

let of_string s = of_bytes (Bytes.of_string s)
let to_string s = Bytes.to_string (to_bytes s)
let string_ = {
  r_of = of_string;
  r_to = to_string;
}

let string = typed string_ (!! T.string)

let rec of_list f = function
| [] -> ValInt 0
| x :: l -> ValBlk (0, [| f x; of_list f l |])

let rec to_list f = function
| ValInt 0 -> []
| ValBlk (0, [|v; vl|]) -> f v :: to_list f vl
| _ -> assert false

let list_ r = {
  r_of = (fun l -> of_list r.r_of l);
  r_to = (fun l -> to_list r.r_to l);
}

let list (r,t) = typed (list_ r) (! T.list [default t])

let of_closure cls = ValCls cls

let to_closure = Tac2val.to_closure

let closure = {
  r_of = of_closure;
  r_to = to_closure;
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
let constr_ = repr_ext val_constr
let constr = typed constr_ (!! T.constr)

let of_preterm c = of_ext val_preterm c
let to_preterm c = to_ext val_preterm c
let preterm_ = repr_ext val_preterm
let preterm = typed preterm_ (!! T.preterm)

let of_cast c = of_ext val_cast c
let to_cast c = to_ext val_cast c
let cast_ = repr_ext val_cast
let cast = typed cast_ (!! T.cast)

let of_ident c = of_ext val_ident c
let to_ident c = to_ext val_ident c
let ident_ = repr_ext val_ident
let ident = typed ident_ (!! T.ident)

let of_pattern c = of_ext val_pattern c
let to_pattern c = to_ext val_pattern c
let pattern_ = repr_ext val_pattern
let pattern = typed pattern_ (!! T.pattern)

let of_evar ev = of_ext val_evar ev
let to_evar ev = to_ext val_evar ev
let evar_ = repr_ext val_evar
let evar = typed evar_ (!! T.evar)

let internal_err =
  let open Names in
  let coq_prefix =
    MPfile (DirPath.make (List.map Id.of_string ["Init"; "Ltac2"]))
  in
  KerName.make coq_prefix (Label.of_id (Id.of_string "Internal"))

let of_exninfo = of_ext val_exninfo
let to_exninfo = to_ext val_exninfo

let exninfo_ = {
  r_of = of_exninfo;
  r_to = to_exninfo;
}
let exninfo = typed exninfo_ (!! T.exninfo)

let of_err e = of_ext val_exn e
let to_err e = to_ext val_exn e
let err_ = repr_ext val_exn
let err = typed err_ (!! T.err)

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

let exn_ = {
  r_of = of_exn;
  r_to = to_exn;
}

let exn = typed exn_ (!! T.exn)

let of_option f = function
| None -> ValInt 0
| Some c -> ValBlk (0, [|f c|])

let to_option f = function
| ValInt 0 -> None
| ValBlk (0, [|c|]) -> Some (f c)
| _ -> assert false

let option_ r = {
  r_of = (fun l -> of_option r.r_of l);
  r_to = (fun l -> to_option r.r_to l);
}

let option (r,t) = typed (option_ r) (! T.option [default t])

let of_pp c = of_ext val_pp c
let to_pp c = to_ext val_pp c
let pp_ = repr_ext val_pp
let pp = typed pp_ (!! T.message)

let of_tuple cl = ValBlk (0, cl)
let to_tuple = function
| ValBlk (0, cl) -> cl
| _ -> assert false

let of_pair f g (x, y) = ValBlk (0, [|f x; g y|])
let to_pair f g = function
| ValBlk (0, [|x; y|]) -> (f x, g y)
| _ -> assert false
let pair_ r0 r1 = {
  r_of = (fun p -> of_pair r0.r_of r1.r_of p);
  r_to = (fun p -> to_pair r0.r_to r1.r_to p);
}
let pair (r0,t0) (r1,t1) = typed (pair_ r0 r1) (tuple [default t0; default t1])


let of_triple f g h (x, y, z) = ValBlk (0, [|f x; g y; h z|])
let to_triple f g h = function
| ValBlk (0, [|x; y; z|]) -> (f x, g y, h z)
| _ -> assert false
let triple_ r0 r1 r2 = {
  r_of = (fun p -> of_triple r0.r_of r1.r_of r2.r_of p);
  r_to = (fun p -> to_triple r0.r_to r1.r_to r2.r_to p);
}
let triple (r0,t0) (r1,t1) (r2,t2) = typed (triple_ r0 r1 r2) (tuple [default t0; default t1; default t2])

let of_array f vl = ValBlk (0, Array.map f vl)
let to_array f = function
| ValBlk (0, vl) -> Array.map f vl
| _ -> assert false
let array_ r = {
  r_of = (fun l -> of_array r.r_of l);
  r_to = (fun l -> to_array r.r_to l);
}
let array (r,t) = typed (array_ r) (! T.array [default t])

let of_block (n, args) = ValBlk (n, args)
let to_block = function
| ValBlk (n, args) -> (n, args)
| _ -> assert false

let block = {
  r_of = of_block;
  r_to = to_block;
}

let of_result r = function
  | Ok x -> of_block (0, [|r x|])
  | Error x -> of_block (1, [|of_exn x|])

let to_result r = function
  | ValBlk (0, [|x|]) -> Ok (r x)
  | ValBlk (1, [|x|]) -> Error (to_exn x)
  | _ -> assert false

let result_ r = {
  r_of = of_result r.r_of;
  r_to = to_result r.r_to;
}
let result (r,t) = typed (result_ r) (! T.result [default t])

let of_open (kn, args) = ValOpn (kn, args)

let to_open = function
| ValOpn (kn, args) -> (kn, args)
| _ -> assert false

let open_ = {
  r_of = of_open;
  r_to = to_open;
}

let of_uint63 n = of_ext val_uint63 n
let to_uint63 x = to_ext val_uint63 x

let uint63_ = {
  r_of = of_uint63;
  r_to = to_uint63;
}
let uint63 = typed uint63_ (!! T.uint63)

let of_float f = of_ext val_float f
let to_float x = to_ext val_float x

let float_ = {
  r_of = of_float;
  r_to = to_float;
}
let float = typed float_ (!! T.float)

let of_constant c = of_ext val_constant c
let to_constant c = to_ext val_constant c
let constant_ = repr_ext val_constant
let constant = typed constant_ (!! T.constant)

let of_reference = let open Names.GlobRef in function
| VarRef id -> ValBlk (0, [| of_ident id |])
| ConstRef cst -> ValBlk (1, [| of_constant cst |])
| IndRef ind -> ValBlk (2, [| of_ext val_inductive ind |])
| ConstructRef cstr -> ValBlk (3, [| of_ext val_constructor cstr |])

let to_reference = let open Names.GlobRef in function
| ValBlk (0, [| id |]) -> VarRef (to_ident id)
| ValBlk (1, [| cst |]) -> ConstRef (to_constant cst)
| ValBlk (2, [| ind |]) -> IndRef (to_ext val_inductive ind)
| ValBlk (3, [| cstr |]) -> ConstructRef (to_ext val_constructor cstr)
| _ -> assert false

let reference_ = {
  r_of = of_reference;
  r_to = to_reference;
}
let reference = typed reference_ (!! T.reference)

(* f is supposed to be pure (unit -> 'a tactic with any effects inside the tactic) *)
let thaw f = f ()

let to_fun1 r0 r' f =
  let f x =
    Proofview.Monad.map r' @@ Tac2val.apply (to_closure f) [r0 x]
  in
  f

let of_fun1 r0 r' f =
  of_closure @@
  Tac2val.abstract 1 (function
      | [x] -> Proofview.Monad.map r' @@ f (r0 x)
      | _ -> assert false)

let fun1_ r r' = make_repr (of_fun1 r.r_to r'.r_of) (to_fun1 r.r_of r'.r_to)
let fun1 (r,t) (r',t') = fun1_ r r', Some Types.(default t @-> default t')

let thunk r = fun1 unit r

let to_fun2 r0 r1 r' f =
  let f x y =
    Proofview.Monad.map r' @@
    Tac2val.apply (to_closure f) [r0 x; r1 y]
  in
  f

let of_fun2 r0 r1 r' f =
  of_closure @@
  Tac2val.abstract 2 (function
      | [x;y] -> Proofview.Monad.map r' @@ f (r0 x) (r1 y)
      | _ -> assert false)

let fun2_ r0 r1 r' = make_repr (of_fun2 r0.r_to r1.r_to r'.r_of) (to_fun2 r0.r_of r1.r_of r'.r_to)
let fun2 (r0,t0) (r1,t1) (r',t') = fun2_ r0 r1 r', Some Types.(default t0 @-> default t1 @-> default t')

let to_fun3 r0 r1 r2 r' f =
  let f x y z =
    Proofview.Monad.map r' @@
    Tac2val.apply (to_closure f) [r0 x; r1 y; r2 z]
  in
  f

let of_fun3 r0 r1 r2 r' f =
  of_closure @@
  Tac2val.abstract 3 (function
      | [x;y;z] -> Proofview.Monad.map r' @@ f (r0 x) (r1 y) (r2 z)
      | _ -> assert false)

let fun3_ r0 r1 r2 r' = make_repr (of_fun3 r0.r_to r1.r_to r2.r_to r'.r_of) (to_fun3 r0.r_of r1.r_of r2.r_of r'.r_to)
let fun3 (r0,t0) (r1,t1) (r2,t2) (r',t') =
  fun3_ r0 r1 r2 r', Some Types.(default t0 @-> default t1 @-> default t2 @-> default t')
