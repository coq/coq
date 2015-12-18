(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util

module Val = Dyn.Make(struct end)

type argument_type =
  (* Basic types *)
  | IntOrVarArgType
  | IdentArgType
  | VarArgType
  (* Specific types *)
  | ConstrArgType
  | ConstrMayEvalArgType
  | OpenConstrArgType
  | ListArgType of argument_type
  | OptArgType of argument_type
  | PairArgType of argument_type * argument_type
  | ExtraArgType of string

let rec argument_type_eq arg1 arg2 = match arg1, arg2 with
| IntOrVarArgType, IntOrVarArgType -> true
| IdentArgType, IdentArgType -> true
| VarArgType, VarArgType -> true
| ConstrArgType, ConstrArgType -> true
| ConstrMayEvalArgType, ConstrMayEvalArgType -> true
| OpenConstrArgType, OpenConstrArgType -> true
| ListArgType arg1, ListArgType arg2 -> argument_type_eq arg1 arg2
| OptArgType arg1, OptArgType arg2 -> argument_type_eq arg1 arg2
| PairArgType (arg1l, arg1r), PairArgType (arg2l, arg2r) ->
  argument_type_eq arg1l arg2l && argument_type_eq arg1r arg2r
| ExtraArgType s1, ExtraArgType s2 -> CString.equal s1 s2
| _ -> false

let rec pr_argument_type = function
| IntOrVarArgType -> str "int_or_var"
| IdentArgType -> str "ident"
| VarArgType -> str "var"
| ConstrArgType -> str "constr"
| ConstrMayEvalArgType -> str "constr_may_eval"
| OpenConstrArgType -> str "open_constr"
| ListArgType t -> pr_argument_type t ++ spc () ++ str "list"
| OptArgType t -> pr_argument_type t ++ spc () ++ str "opt"
| PairArgType (t1, t2) ->
    str "("++ pr_argument_type t1 ++ spc () ++
    str "*" ++ spc () ++ pr_argument_type t2 ++ str ")"
| ExtraArgType s -> str s

type ('raw, 'glob, 'top) genarg_type = argument_type

type 'a uniform_genarg_type = ('a, 'a, 'a) genarg_type
(** Alias for concision *)

(* Dynamics but tagged by a type expression *)

type rlevel
type glevel
type tlevel

type 'a generic_argument = argument_type * Obj.t
type raw_generic_argument = rlevel generic_argument
type glob_generic_argument = glevel generic_argument
type typed_generic_argument = tlevel generic_argument

let rawwit t = t
let glbwit t = t
let topwit t = t

let wit_list t = ListArgType t

let wit_opt t = OptArgType t

let wit_pair t1 t2 = PairArgType (t1,t2)

let in_gen t o = (t,Obj.repr o)
let out_gen t (t',o) = if argument_type_eq t t' then Obj.magic o else failwith "out_gen"
let genarg_tag (s,_) = s

let has_type (t, v) u = argument_type_eq t u

let unquote x = x

type ('a,'b) abstract_argument_type = argument_type
type 'a raw_abstract_argument_type = ('a,rlevel) abstract_argument_type
type 'a glob_abstract_argument_type = ('a,glevel) abstract_argument_type
type 'a typed_abstract_argument_type = ('a,tlevel) abstract_argument_type

type ('a, 'b, 'c, 'l) cast = Obj.t

let raw = Obj.obj
let glb = Obj.obj
let top = Obj.obj

type ('r, 'l) unpacker =
  { unpacker : 'a 'b 'c. ('a, 'b, 'c) genarg_type -> ('a, 'b, 'c, 'l) cast -> 'r }

let unpack pack (t, obj) = pack.unpacker t (Obj.obj obj)

(** Type transformers *)

type ('r, 'l) list_unpacker =
  { list_unpacker : 'a 'b 'c. ('a, 'b, 'c) genarg_type ->
    ('a list, 'b list, 'c list, 'l) cast -> 'r }

let list_unpack pack (t, obj) = match t with
| ListArgType t -> pack.list_unpacker t (Obj.obj obj)
| _ -> failwith "out_gen"

type ('r, 'l) opt_unpacker =
  { opt_unpacker : 'a 'b 'c. ('a, 'b, 'c) genarg_type ->
    ('a option, 'b option, 'c option, 'l) cast -> 'r }

let opt_unpack pack (t, obj) = match t with
| OptArgType t -> pack.opt_unpacker t (Obj.obj obj)
| _ -> failwith "out_gen"

type ('r, 'l) pair_unpacker =
  { pair_unpacker : 'a1 'a2 'b1 'b2 'c1 'c2.
    ('a1, 'b1, 'c1) genarg_type -> ('a2, 'b2, 'c2) genarg_type ->
    (('a1 * 'a2), ('b1 * 'b2), ('c1 * 'c2), 'l) cast -> 'r }

let pair_unpack pack (t, obj) = match t with
| PairArgType (t1, t2) -> pack.pair_unpacker t1 t2 (Obj.obj obj)
| _ -> failwith "out_gen"

(** Creating args *)

type load = {
  nil : Obj.t option;
  dyn : Obj.t Val.tag;
}

let (arg0_map : load String.Map.t ref) = ref String.Map.empty

let cast_tag : 'a Val.tag -> 'b Val.tag = Obj.magic

let create_arg opt ?dyn name =
  if String.Map.mem name !arg0_map then
    Errors.anomaly (str "generic argument already declared: " ++ str name)
  else
    let dyn = match dyn with None -> Val.create name | Some dyn -> cast_tag dyn in
    let obj = { nil = Option.map Obj.repr opt; dyn; } in
    let () = arg0_map := String.Map.add name obj !arg0_map in
    ExtraArgType name

let make0 = create_arg

let default_empty_value t =
  let rec aux = function
  | ListArgType _ -> Some (Obj.repr [])
  | OptArgType _ -> Some (Obj.repr None)
  | PairArgType(t1, t2) ->
      (match aux t1, aux t2 with
      | Some v1, Some v2 -> Some (Obj.repr (v1, v2))
      | _ -> None)
  | ExtraArgType s ->
    (String.Map.find s !arg0_map).nil
  | _ -> None in
  match aux t with
  | Some v -> Some (Obj.obj v)
  | None -> None

(** Beware: keep in sync with the corresponding types *)
let int_or_var_T = Val.create "int_or_var"
let ident_T = Val.create "ident"
let var_T = Val.create "var"
let genarg_T = Val.create "genarg"
let constr_T = Val.create "constr"
let constr_may_eval_T = Val.create "constr_may_eval"
let open_constr_T = Val.create "open_constr"

let option_val = Val.create "option"
let list_val = Val.create "list"
let pair_val = Val.create "pair"

let val_tag = function
| IntOrVarArgType -> cast_tag int_or_var_T
| IdentArgType -> cast_tag ident_T
| VarArgType -> cast_tag var_T
| ConstrArgType -> cast_tag constr_T
| ConstrMayEvalArgType -> cast_tag constr_may_eval_T
| OpenConstrArgType -> cast_tag open_constr_T
| ExtraArgType s -> Obj.magic (String.Map.find s !arg0_map).dyn
(** Recursive types have no associated dynamic tag *)
| ListArgType t -> assert false
| OptArgType t -> assert false
| PairArgType (t1, t2) -> assert false

exception CastError of argument_type * Val.t

let prj : type a. a Val.tag -> Val.t -> a option = fun t v ->
  let Val.Dyn (t', x) = v in
  match Val.eq t t' with
  | None -> None
  | Some Refl -> Some x

let try_prj wit v = match prj (val_tag wit) v with
| None -> raise (CastError (wit, v))
| Some x -> x

let rec val_cast : type a. a typed_abstract_argument_type -> Val.t -> a =
fun wit v -> match unquote wit with
| IntOrVarArgType | IdentArgType
| VarArgType
| ConstrArgType | ConstrMayEvalArgType
| OpenConstrArgType | ExtraArgType _ -> try_prj wit v
| ListArgType t ->
  let v = match prj list_val v with
  | None -> raise (CastError (wit, v))
  | Some v -> v
  in
  Obj.magic (List.map (fun x -> val_cast t x) v)
| OptArgType t ->
  let v = match prj option_val v with
  | None -> raise (CastError (wit, v))
  | Some v -> v
  in
  Obj.magic (Option.map (fun x -> val_cast t x) v)
| PairArgType (t1, t2) ->
  let (v1, v2) = match prj pair_val v with
  | None -> raise (CastError (wit, v))
  | Some v -> v
  in
  Obj.magic (val_cast t1 v1, val_cast t2 v2)

(** Registering genarg-manipulating functions *)

module type GenObj =
sig
  type ('raw, 'glb, 'top) obj
  val name : string
  val default : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb, 'top) obj option
end

module Register (M : GenObj) =
struct
  let arg0_map =
    ref (String.Map.empty : (Obj.t, Obj.t, Obj.t) M.obj String.Map.t)

  let register0 arg f = match arg with
  | ExtraArgType s ->
    if String.Map.mem s !arg0_map then
      let msg = str M.name ++ str " function already registered: " ++ str s in
      Errors.anomaly msg
    else
      arg0_map := String.Map.add s (Obj.magic f) !arg0_map
  | _ -> assert false

  let get_obj0 name =
    try String.Map.find name !arg0_map
    with Not_found ->
      match M.default (ExtraArgType name) with
      | None ->
        Errors.anomaly (str M.name ++ str " function not found: " ++ str name)
      | Some obj -> obj

  (** For now, the following function is quite dummy and should only be applied
      to an extra argument type, otherwise, it will badly fail. *)
  let obj t = match t with
  | ExtraArgType s -> Obj.magic (get_obj0 s)
  | _ -> assert false

end

(** Hackish part *)

let arg0_names = ref (String.Map.empty : string String.Map.t)
(** We use this table to associate a name to a given witness, to use it with
    the extension mechanism. This is REALLY ad-hoc, but I do not know how to
    do so nicely either. *)

let register_name0 t name = match t with
| ExtraArgType s ->
  let () = assert (not (String.Map.mem s !arg0_names)) in
  arg0_names := String.Map.add s name !arg0_names
| _ -> failwith "register_name0"

let get_name0 name =
  String.Map.find name !arg0_names
