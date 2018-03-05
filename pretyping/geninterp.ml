(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genarg

module TacStore = Store.Make ()

(** Dynamic toplevel values *)

module ValT = Dyn.Make ()

module Val =
struct

  type 'a typ = 'a ValT.tag

  type _ tag =
  | Base : 'a typ -> 'a tag
  | List : 'a tag -> 'a list tag
  | Opt : 'a tag -> 'a option tag
  | Pair : 'a tag * 'b tag -> ('a * 'b) tag

  type t = Dyn : 'a typ * 'a -> t

  let eq = ValT.eq
  let repr = ValT.repr
  let create = ValT.create

  let pr : type a. a typ -> Pp.t = fun t -> Pp.str (repr t)

  let typ_list = ValT.create "list"
  let typ_opt = ValT.create "option"
  let typ_pair = ValT.create "pair"

  let rec inject : type a. a tag -> a -> t = fun tag x -> match tag with
  | Base t -> Dyn (t, x)
  | List tag -> Dyn (typ_list, List.map (fun x -> inject tag x) x)
  | Opt tag -> Dyn (typ_opt, Option.map (fun x -> inject tag x) x)
  | Pair (tag1, tag2) ->
    Dyn (typ_pair, (inject tag1 (fst x), inject tag2 (snd x)))

end

module ValTMap = ValT.Map

module ValReprObj =
struct
  type ('raw, 'glb, 'top) obj = 'top Val.tag
  let name = "valrepr"
  let default _ = None
end

module ValRepr = Register(ValReprObj)

let rec val_tag : type a b c. (a, b, c) genarg_type -> c Val.tag = function
| ListArg t -> Val.List (val_tag t)
| OptArg t -> Val.Opt (val_tag t)
| PairArg (t1, t2) -> Val.Pair (val_tag t1, val_tag t2)
| ExtraArg s -> ValRepr.obj (ExtraArg s)

let val_tag = function Topwit t -> val_tag t

let register_val0 wit tag =
  let tag = match tag with
  | None ->
    let name = match wit with
    | ExtraArg s -> ArgT.repr s
    | _ -> assert false
    in
    Val.Base (Val.create name)
  | Some tag -> tag
  in
  ValRepr.register0 wit tag

(** Interpretation functions *)

type interp_sign = {
  lfun : Val.t Id.Map.t;
  extra : TacStore.t }

type ('glb, 'top) interp_fun = interp_sign -> 'glb -> 'top Ftactic.t

module InterpObj =
struct
  type ('raw, 'glb, 'top) obj = ('glb, Val.t) interp_fun
  let name = "interp"
  let default _ = None
end

module Interp = Register(InterpObj)

let interp = Interp.obj

let register_interp0 = Interp.register0
