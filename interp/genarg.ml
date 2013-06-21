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

type argument_type =
  (* Basic types *)
  | IntOrVarArgType
  | IntroPatternArgType
  | IdentArgType of bool
  | VarArgType
  | RefArgType
  (* Specific types *)
  | GenArgType
  | SortArgType
  | ConstrArgType
  | ConstrMayEvalArgType
  | QuantHypArgType
  | OpenConstrArgType of bool
  | ConstrWithBindingsArgType
  | BindingsArgType
  | RedExprArgType
  | List0ArgType of argument_type
  | List1ArgType of argument_type
  | OptArgType of argument_type
  | PairArgType of argument_type * argument_type
  | ExtraArgType of string

let rec argument_type_eq arg1 arg2 = match arg1, arg2 with
| IntOrVarArgType, IntOrVarArgType -> true
| IntroPatternArgType, IntroPatternArgType -> true
| IdentArgType b1, IdentArgType b2 -> (b1 : bool) == b2
| VarArgType, VarArgType -> true
| RefArgType, RefArgType -> true
| GenArgType, GenArgType -> true
| SortArgType, SortArgType -> true
| ConstrArgType, ConstrArgType -> true
| ConstrMayEvalArgType, ConstrMayEvalArgType -> true
| QuantHypArgType, QuantHypArgType -> true
| OpenConstrArgType b1, OpenConstrArgType b2 -> (b1 : bool) == b2
| ConstrWithBindingsArgType, ConstrWithBindingsArgType -> true
| BindingsArgType, BindingsArgType -> true
| RedExprArgType, RedExprArgType -> true
| List0ArgType arg1, List0ArgType arg2 -> argument_type_eq arg1 arg2
| List1ArgType arg1, List1ArgType arg2 -> argument_type_eq arg1 arg2
| OptArgType arg1, OptArgType arg2 -> argument_type_eq arg1 arg2
| PairArgType (arg1l, arg1r), PairArgType (arg2l, arg2r) ->
  argument_type_eq arg1l arg2l && argument_type_eq arg1r arg2r
| ExtraArgType s1, ExtraArgType s2 -> CString.equal s1 s2
| _ -> false

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

let wit_list0 t = List0ArgType t

let wit_list1 t = List1ArgType t

let wit_opt t = OptArgType t

let wit_pair t1 t2 = PairArgType (t1,t2)

let in_gen t o = (t,Obj.repr o)
let out_gen t (t',o) = if argument_type_eq t t' then Obj.magic o else failwith "out_gen"
let genarg_tag (s,_) = s

let fold_list0 f = function
  | (List0ArgType t, l) ->
      List.fold_right (fun x -> f (in_gen t x)) (Obj.magic l)
  | _ -> failwith "Genarg: not a list0"

let fold_list1 f = function
  | (List1ArgType t, l) ->
      List.fold_right (fun x -> f (in_gen t x)) (Obj.magic l)
  | _ -> failwith "Genarg: not a list1"

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

let app_list0 f = function
  | (List0ArgType t as u, l) ->
      let o = Obj.magic l in
      (u, Obj.repr (List.map (fun x -> out_gen t (f (in_gen t x))) o))
  | _ -> failwith "Genarg: not a list0"

let app_list1 f = function
  | (List1ArgType t as u, l) ->
      let o = Obj.magic l in
      (u, Obj.repr (List.map (fun x -> out_gen t (f (in_gen t x))) o))
  | _ -> failwith "Genarg: not a list1"

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

let has_type (t, v) u = argument_type_eq t u

let unquote x = x

type an_arg_of_this_type = Obj.t

let in_generic t x = (t, Obj.repr x)

type ('a,'b) abstract_argument_type = argument_type
type 'a raw_abstract_argument_type = ('a,rlevel) abstract_argument_type
type 'a glob_abstract_argument_type = ('a,glevel) abstract_argument_type
type 'a typed_abstract_argument_type = ('a,tlevel) abstract_argument_type

(** New interface for genargs. *)

type glob_sign = {
  ltacvars : Id.t list * Id.t list;
  ltacrecvars : (Id.t * Nametab.ltac_constant) list;
  gsigma : Evd.evar_map;
  genv : Environ.env }

module TacStore = Store.Make(struct end)

type interp_sign = {
  lfun : (Id.t * tlevel generic_argument) list;
  extra : TacStore.t }

type ('raw, 'glb, 'top) arg0 = {
  arg0_rprint : 'raw -> std_ppcmds;
  arg0_gprint : 'glb -> std_ppcmds;
  arg0_tprint : 'top -> std_ppcmds;
  arg0_glob : glob_sign -> 'raw -> glob_sign * 'glb;
  arg0_subst : Mod_subst.substitution -> 'glb -> 'glb;
  arg0_interp : interp_sign ->
    Goal.goal Evd.sigma -> 'glb -> Evd.evar_map * 'top;
}

let default_arg0 name = {
  arg0_rprint = (fun _ -> str "<abstract>");
  arg0_gprint = (fun _ -> str "<abstract>");
  arg0_tprint = (fun _ -> str "<abstract>");
  arg0_glob = (fun _ _ -> failwith ("undefined globalizer for " ^ name));
  arg0_subst = (fun _ _ -> failwith ("undefined substitutor for " ^ name));
  arg0_interp = (fun _ _ _ -> failwith ("undefined interpreter for " ^ name));
}

let default_uniform_arg0 name = {
  arg0_rprint = (fun _ -> str "<abstract>");
  arg0_gprint = (fun _ -> str "<abstract>");
  arg0_tprint = (fun _ -> str "<abstract>");
  arg0_glob = (fun ist x -> (ist, x));
  arg0_subst = (fun _ x -> x);
  arg0_interp = (fun _ gl x -> (gl.Evd.sigma, x));
}

let arg0_map = ref (String.Map.empty : (Obj.t * Obj.t option) String.Map.t)
(** First component is the argument itself, second is the default raw
    inhabitant. *)

let make0 def name arg =
  let () =
    if String.Map.mem name !arg0_map then
      Errors.anomaly (str "Genarg " ++ str name ++ str " already defined")
  in
  let arg = Obj.repr arg in
  let def = Obj.magic def in
  let () = arg0_map := String.Map.add name (arg, def) !arg0_map in
  ExtraArgType name

let get_obj name =
  let (obj, _) = String.Map.find name !arg0_map in
  (Obj.obj obj : (Obj.t, Obj.t, Obj.t) arg0)

(** For now, the following functions are quite dummy and should only be applied
    to an extra argument type, otherwise, they will badly fail. *)

let arg_gen = function
| ExtraArgType name -> Obj.magic (get_obj name)
| _ -> assert false

let rec raw_print (tpe, v) = match tpe with
| ExtraArgType name ->
  let obj = get_obj name in
  obj.arg0_rprint v
| _ -> assert false (* TODO *)

let rec glb_print (tpe, v) = match tpe with
| ExtraArgType name ->
  let obj = get_obj name in
  obj.arg0_gprint v
| _ -> assert false (* TODO *)

let rec top_print (tpe, v) = match tpe with
| ExtraArgType name ->
  let obj = get_obj name in
  obj.arg0_rprint v
| _ -> assert false (* TODO *)

let rec globalize ist (tpe, v) = match tpe with
| ExtraArgType name ->
  let obj = get_obj name in
  let (ist, ans) = obj.arg0_glob ist v in
  (ist, (tpe, ans))
| _ -> assert false (* TODO *)

let rec substitute subst (tpe, v) = match tpe with
| ExtraArgType name ->
  let obj = get_obj name in
  (tpe, obj.arg0_subst subst v)
| _ -> assert false (* TODO *)

let rec interpret ist gl (tpe, v) = match tpe with
| ExtraArgType name ->
  let obj = get_obj name in
  let (ist, ans) = obj.arg0_interp ist gl v in
  (ist, (tpe, ans))
| _ -> assert false (* TODO *)

(** Compatibility layer *)

let create_arg v s = make0 v s (default_arg0 s)

let default_empty_value t =
  let rec aux = function
  | List0ArgType _ -> Some (Obj.repr [])
  | OptArgType _ -> Some (Obj.repr None)
  | PairArgType(t1,t2) ->
      (match aux t1, aux t2 with
      | Some v1, Some v2 -> Some (Obj.repr (v1, v2))
      | _ -> None)
  | ExtraArgType s ->
    let (_, def) = String.Map.find s !arg0_map in
    def
  | _ -> None in
  match aux t with
  | Some v -> Some (Obj.obj v)
  | None -> None

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
