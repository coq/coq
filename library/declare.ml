
(* $Id$ *)

open Util
open Names
open Constant
open Inductive
open Libobject
open Lib
open Impargs

(* Variables. *)

let cache_variable (_,obj) = 
  Global.push_var obj

let load_variable _ = 
  anomaly "we shouldn't load a variable"

let open_variable _ = 
  anomaly "we shouldn't open a variable"

let specification_variable _ = 
  anomaly "we shouldn't extract the specification of a variable"

let (in_variable, out_variable) =
  let od = {
    cache_function = cache_variable;
    load_function = load_variable;
    open_function = open_variable;
    specification_function = specification_variable } in
  declare_object ("Variable", od)

let declare_variable id c =
  let obj = (id,c) in
  Global.push_var obj;
  let _ = add_leaf id CCI (in_variable obj) in
  ()

(* Parameters. *)

let cache_parameter (sp,c) =
  Global.add_parameter sp c;
  Nametab.push (basename sp) sp

let load_parameter (sp,_) =
  let cb = Global.lookup_constant sp in
  Global.add_constraints cb.const_constraints
  
let open_parameter (sp,_) =
  Nametab.push (basename sp) sp

let specification_parameter obj = obj

let (in_parameter, out_parameter) =
  let od = {
    cache_function = cache_parameter;
    load_function = load_parameter;
    open_function = open_parameter;
    specification_function = specification_parameter } in
  declare_object ("Parameter", od)

let declare_parameter id c =
  let sp = add_leaf id CCI (in_parameter c) in
  Global.add_parameter sp c;
  Nametab.push (basename sp) sp
 
(* Constants. *)

let cache_constant (sp,ce) =
  Global.add_constant sp ce;
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp

let load_constant (sp,_) =
  let cb = Global.lookup_constant sp in
  Global.add_constraints cb.const_constraints
  
let open_constant (sp,_) =
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp

let specification_constant obj = obj

let (in_constant, out_constant) =
  let od = {
    cache_function = cache_constant;
    load_function = load_constant;
    open_function = open_constant;
    specification_function = specification_constant } in
  declare_object ("Constant", od)

let declare_constant id ce =
  let sp = add_leaf id CCI (in_constant ce) in
  Global.add_constant sp ce;
  Nametab.push (basename sp) sp;
  declare_constant_implicits sp
 
(* Inductives. *)

let push_inductive_names sp mie =
  List.iter
    (fun (id,_,cnames,_) ->
       Nametab.push id sp;
       List.iter (fun x -> Nametab.push x sp) cnames)
    mie.mind_entry_inds

let cache_inductive (sp,mie) =
  Global.add_mind sp mie;
  push_inductive_names sp mie;
  declare_inductive_implicits sp

let load_inductive (sp,_) =
  let mib = Global.lookup_mind sp in
  Global.add_constraints mib.mind_constraints
  
let open_inductive (sp,mie) =
  push_inductive_names sp mie;
  declare_inductive_implicits sp

let specification_inductive obj = obj

let (in_inductive, out_inductive) =
  let od = {
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    specification_function = specification_inductive } in
  declare_object ("Inductive", od)

let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | (id,_,_,_)::_ -> id
    | [] -> anomaly "cannot declare an empty list of inductives"
  in
  let sp = add_leaf id CCI (in_inductive mie) in
  Global.add_mind sp mie;
  push_inductive_names sp mie;
  declare_inductive_implicits sp

