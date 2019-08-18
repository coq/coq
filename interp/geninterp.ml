(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genarg
open Valinterp

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

module TacStore = Store.Make ()

type interp_sign =
  { lfun : Val.t Id.Map.t
  ; poly : bool
  ; extra : TacStore.t }

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
