
(* $Id$ *)

open Names
open Term
open Reduction
open Declarations
open Environ
open Inductive

type implicits =
  | Impl_auto of int list
  | Impl_manual of int list
  | No_impl

let implicit_args = ref false

let make_implicit_args flag = implicit_args := flag
let is_implicit_args () = !implicit_args

let with_implicits b f x =
  let oimplicit = !implicit_args in
  try 
    implicit_args := b;
    let rslt = f x in 
    implicit_args := oimplicit;
    rslt
  with e -> begin
    implicit_args := oimplicit;
    raise e
  end

let implicitely f = with_implicits true f

let using_implicits = function
  | No_impl -> with_implicits false
  | _ -> with_implicits true

let auto_implicits env ty = Impl_auto (poly_args env Evd.empty ty)

let list_of_implicits = function 
  | Impl_auto l -> l
  | Impl_manual l -> l
  | No_impl -> []

(* Constants. *)

let constants_table = ref Spmap.empty

let declare_constant_implicits sp =
  let env = Global.env () in
  let cb = lookup_constant sp env in
  let imps = auto_implicits env (body_of_type cb.const_type) in
  constants_table := Spmap.add sp imps !constants_table

let declare_constant_manual_implicits sp imps =
  constants_table := Spmap.add sp (Impl_manual imps) !constants_table

let constant_implicits sp =
  try Spmap.find sp !constants_table with Not_found -> No_impl

let constant_implicits_list sp =
  list_of_implicits (constant_implicits sp)

(* Inductives and constructors. Their implicit arguments are stored
   in an array, indexed by the inductive number, of pairs $(i,v)$ where
   $i$ are the implicit arguments of the inductive and $v$ the array of 
   implicit arguments of the constructors. *)

let inductives_table = ref Spmap.empty

let declare_inductive_implicits sp =
  let env = Global.env () in
  let mib = lookup_mind sp env in
  let env_ar = push_rels (mind_arities_context mib) env in
  let imps_one_inductive mip =
    (auto_implicits env (body_of_type (mind_user_arity mip)),
     Array.map (fun c -> auto_implicits env_ar (body_of_type c))
       (mind_user_lc mip))
  in
  let imps = Array.map imps_one_inductive mib.mind_packets in
  inductives_table := Spmap.add sp imps !inductives_table
    
let inductive_implicits (sp,i) =
  try
    let imps = Spmap.find sp !inductives_table in fst imps.(i)
  with Not_found -> 
    No_impl

let constructor_implicits ((sp,i),j) =
  try
    let imps = Spmap.find sp !inductives_table in (snd imps.(i)).(pred j)
  with Not_found -> 
    No_impl

let constructor_implicits_list constr_sp = 
  list_of_implicits (constructor_implicits constr_sp)

let inductive_implicits_list ind_sp =
  list_of_implicits (inductive_implicits ind_sp)

(* Variables. *)

let var_table = ref Idmap.empty

let declare_var_implicits id =
  let env = Global.env () in
  let (_,ty) = lookup_named id env in
  let imps = auto_implicits env (body_of_type ty) in
  var_table := Idmap.add id imps !var_table

let implicits_of_var id =
  list_of_implicits (try Idmap.find id !var_table with Not_found -> No_impl)

(* Tests if declared implicit *)

let is_implicit_constant sp =
  try let _ = Spmap.find sp !constants_table in true with Not_found -> false

let is_implicit_inductive_definition sp =
  try let _ = Spmap.find sp !inductives_table in true with Not_found -> false

let is_implicit_var id =
  try let _ = Idmap.find id !var_table in true with Not_found -> false

(* Registration as global tables and roolback. *)

type frozen_t = bool
              * implicits Spmap.t 
              * (implicits * implicits array) array Spmap.t 
              * implicits Idmap.t

let init () =
  constants_table := Spmap.empty;
  inductives_table := Spmap.empty;
  var_table := Idmap.empty

let freeze () =
  (!implicit_args, !constants_table, !inductives_table, !var_table)

let unfreeze (imps,ct,it,vt) =
  implicit_args := imps;
  constants_table := ct;
  inductives_table := it;
  var_table := vt

let _ = 
  Summary.declare_summary "implicits"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let rollback f x =
  let fs = freeze () in
  try f x with e -> begin unfreeze fs; raise e end

