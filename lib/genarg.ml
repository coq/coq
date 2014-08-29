(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util

type argument_type =
  (* Basic types *)
  | IntOrVarArgType
  | IdentArgType
  | VarArgType
  (* Specific types *)
  | GenArgType
  | ConstrArgType
  | ConstrMayEvalArgType
  | QuantHypArgType
  | OpenConstrArgType
  | ConstrWithBindingsArgType
  | BindingsArgType
  | RedExprArgType
  | ListArgType of argument_type
  | OptArgType of argument_type
  | PairArgType of argument_type * argument_type
  | ExtraArgType of string

let rec argument_type_eq arg1 arg2 = match arg1, arg2 with
| IntOrVarArgType, IntOrVarArgType -> true
| IdentArgType, IdentArgType -> true
| VarArgType, VarArgType -> true
| GenArgType, GenArgType -> true
| ConstrArgType, ConstrArgType -> true
| ConstrMayEvalArgType, ConstrMayEvalArgType -> true
| QuantHypArgType, QuantHypArgType -> true
| OpenConstrArgType, OpenConstrArgType -> true
| ConstrWithBindingsArgType, ConstrWithBindingsArgType -> true
| BindingsArgType, BindingsArgType -> true
| RedExprArgType, RedExprArgType -> true
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
| GenArgType -> str "genarg"
| ConstrArgType -> str "constr"
| ConstrMayEvalArgType -> str "constr_may_eval"
| QuantHypArgType -> str "qhyp"
| OpenConstrArgType -> str "open_constr"
| ConstrWithBindingsArgType -> str "constr_with_bindings"
| BindingsArgType -> str "bindings"
| RedExprArgType -> str "redexp"
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

let fold_list f = function
  | (ListArgType t, l) ->
      List.fold_right (fun x -> f (in_gen t x)) (Obj.magic l)
  | _ -> failwith "Genarg: not a list"

let fold_opt f a = function
  | (OptArgType t, l) ->
      (match Obj.magic l with
	| None -> a
	| Some x -> f (in_gen t x))
  | _ -> failwith "Genarg: not a opt"

let fold_pair f = function
  | (PairArgType (t1,t2), l) ->
      let (x1,x2) = Obj.magic l in
      f (in_gen t1 x1) (in_gen t2 x2)
  | _ -> failwith "Genarg: not a pair"

let app_list f = function
  | (ListArgType t as u, l) ->
      let o = Obj.magic l in
      (u, Obj.repr (List.map (fun x -> out_gen t (f (in_gen t x))) o))
  | _ -> failwith "Genarg: not a list0"

let app_opt f = function
  | (OptArgType t as u, l) ->
      let o = Obj.magic l in
      (u, Obj.repr (Option.map (fun x -> out_gen t (f (in_gen t x))) o))
  | _ -> failwith "Genarg: not an opt"

let app_pair f1 f2 = function
  | (PairArgType (t1,t2) as u, l) ->
      let (o1,o2) = Obj.magic l in
      let o1 = out_gen t1 (f1 (in_gen t1 o1)) in
      let o2 = out_gen t2 (f2 (in_gen t2 o2)) in
      (u, Obj.repr (o1,o2))
  | _ -> failwith "Genarg: not a pair"

module Monadic (M:Monad.S) = struct

  let app_list f = function
  | (ListArgType t as u, l) ->
      let o = Obj.magic l in
      let open M in
      let apply x =
        f (in_gen t x) >>= fun y ->
        return (out_gen t y)
      in
      M.List.map apply o >>= fun r ->
      return (u, Obj.repr r)
  | _ -> failwith "Genarg: not a list0"

end

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

(** Creating args *)

let (arg0_map : Obj.t option String.Map.t ref) = ref String.Map.empty

let create_arg opt name =
  if String.Map.mem name !arg0_map then
    Errors.anomaly (str "generic argument already declared: " ++ str name)
  else
    let () = arg0_map := String.Map.add name (Obj.magic opt) !arg0_map in
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
    String.Map.find s !arg0_map
  | _ -> None in
  match aux t with
  | Some v -> Some (Obj.obj v)
  | None -> None

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

module Unsafe =
struct

let inj tpe x = (tpe, x)
let prj (_, x) = x

end
