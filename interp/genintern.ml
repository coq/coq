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
open Mod_subst
open Genarg

type glob_sign = {
  ltacvars : Id.Set.t;
  ltacrecvars : (Id.t * Nametab.ltac_constant) list;
  gsigma : Evd.evar_map;
  genv : Environ.env }

type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb
type 'glb subst_fun = substitution -> 'glb -> 'glb

let arg0_intern_map =
  ref (String.Map.empty : (Obj.t, Obj.t) intern_fun String.Map.t)
let arg0_subst_map =
  ref (String.Map.empty : Obj.t subst_fun String.Map.t)

let get_intern0 name =
  try String.Map.find name !arg0_intern_map
  with Not_found ->
    Errors.anomaly (str "intern0 function not found: " ++ str name)

let get_subst0 name =
  try String.Map.find name !arg0_subst_map
  with Not_found ->
    Errors.anomaly (str "subst0 function not found: " ++ str name)

(** For now, the following functions are quite dummy and should only be applied
    to an extra argument type, otherwise, they will badly fail. *)

let rec obj_intern t = match t with
| ExtraArgType s -> get_intern0 s
| _ -> assert false

let intern t = Obj.magic (obj_intern (unquote (rawwit t)))

let generic_intern ist v =
  let t = genarg_tag v in
  let (ist, ans) = obj_intern t ist (Unsafe.prj v) in
  (ist, Unsafe.inj t ans)

(** Substitution functions *)

let rec obj_substitute t = match t with
| ExtraArgType s -> get_subst0 s
| _ -> assert false

let substitute t = Obj.magic (obj_substitute (unquote (rawwit t)))

let generic_substitute subs v =
  let t = genarg_tag v in
  let ans = obj_substitute t subs (Unsafe.prj v) in
  Unsafe.inj t ans

(** Registering functions *)

let register_intern0 arg f = match unquote (rawwit arg) with
| ExtraArgType s ->
  if String.Map.mem s !arg0_intern_map then
    Errors.anomaly (str "intern0 function already registered: " ++ str s)
  else
    arg0_intern_map := String.Map.add s (Obj.magic f) !arg0_intern_map
| _ -> assert false

let register_subst0 arg f = match unquote (rawwit arg) with
| ExtraArgType s ->
  if String.Map.mem s !arg0_subst_map then
    Errors.anomaly (str "subst0 function already registered: " ++ str s)
  else
    arg0_subst_map := String.Map.add s (Obj.magic f) !arg0_subst_map
| _ -> assert false
