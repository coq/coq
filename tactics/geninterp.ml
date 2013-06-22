(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Genarg

module TacStore = Store.Make(struct end)

type interp_sign = {
  lfun : tlevel generic_argument Id.Map.t;
  extra : TacStore.t }

type ('glb, 'top) interp_fun = interp_sign ->
    Goal.goal Evd.sigma -> 'glb -> Evd.evar_map * 'top

let arg0_interp_map =
  ref (String.Map.empty : (Obj.t, Obj.t) interp_fun String.Map.t)

let get_interp0 name =
  try String.Map.find name !arg0_interp_map
  with Not_found ->
    Errors.anomaly (str "interp0 function not found: " ++ str name)

(** For now, the following functions are quite dummy and should only be applied
    to an extra argument type, otherwise, they will badly fail. *)

let rec obj_interp t = match t with
| ExtraArgType s -> get_interp0 s
| _ -> assert false

let interp t = Obj.magic (obj_interp (unquote (rawwit t)))

let generic_interp ist gl v =
  let t = genarg_tag v in
  let (sigma, ans) = obj_interp t ist gl (Unsafe.prj v) in
  (sigma, Unsafe.inj t ans)

(** Registering functions *)

let register_interp0 arg f = match unquote (rawwit arg) with
| ExtraArgType s ->
  if String.Map.mem s !arg0_interp_map then
    Errors.anomaly (str "interp0 function already registered: " ++ str s)
  else
    arg0_interp_map := String.Map.add s (Obj.magic f) !arg0_interp_map
| _ -> assert false
