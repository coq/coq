
(* $Id$ *)

open Names
open Term
open Reduction
open Declarations
open Environ
open Inductive
open Libobject
open Lib

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

(*s Constants. *)

let constants_table = ref Spmap.empty

let compute_constant_implicits sp =
  let env = Global.env () in
  let cb = lookup_constant sp env in
  auto_implicits env (body_of_type cb.const_type)

let cache_constant_implicits (_,(sp,imps)) = 
  constants_table := Spmap.add sp imps !constants_table

let (in_constant_implicits, _) =
  let od = {
    cache_function = cache_constant_implicits;
    load_function = cache_constant_implicits;
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("CONSTANT-IMPLICITS", od)

let declare_constant_implicits sp =
  let imps = compute_constant_implicits sp in
  add_anonymous_leaf (in_constant_implicits (sp,imps))

let constant_implicits sp =
  try Spmap.find sp !constants_table with Not_found -> No_impl

let constant_implicits_list sp =
  list_of_implicits (constant_implicits sp)

(*s Inductives and constructors. Their implicit arguments are stored
   in an array, indexed by the inductive number, of pairs $(i,v)$ where
   $i$ are the implicit arguments of the inductive and $v$ the array of 
   implicit arguments of the constructors. *)

module Inductive_path = struct
  type t = inductive_path
  let compare (spx,ix) (spy,iy) = 
    let c = ix - iy in if c = 0 then sp_ord spx spy else c
end

module Indmap = Map.Make(Inductive_path)

let inductives_table = ref Indmap.empty

module Construtor_path = struct
  type t = constructor_path
  let compare (indx,ix) (indy,iy) = 
    let c = ix - iy in if c = 0 then Inductive_path.compare indx indy else c
end

module Constrmap = Map.Make(Construtor_path)

let inductives_table = ref Indmap.empty

let constructors_table = ref Constrmap.empty

let cache_inductive_implicits (_,(indp,imps)) =
  inductives_table := Indmap.add indp imps !inductives_table

let (in_inductive_implicits, _) =
  let od = {
    cache_function = cache_inductive_implicits;
    load_function = cache_inductive_implicits;
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("INDUCTIVE-IMPLICITS", od)

let cache_constructor_implicits (_,(consp,imps)) =
  constructors_table := Constrmap.add consp imps !constructors_table

let (in_constructor_implicits, _) =
  let od = {
    cache_function = cache_constructor_implicits;
    load_function = cache_constructor_implicits;
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("CONSTRUCTOR-IMPLICITS", od)

let compute_mib_implicits sp =
  let env = Global.env () in
  let mib = lookup_mind sp env in
  let env_ar = push_rels (mind_arities_context mib) env in
  let imps_one_inductive mip =
    (auto_implicits env (body_of_type (mind_user_arity mip)),
     Array.map (fun c -> auto_implicits env_ar (body_of_type c))
       (mind_user_lc mip))
  in
  Array.map imps_one_inductive mib.mind_packets

let cache_mib_implicits (_,(sp,mibimps)) =
  Array.iteri
    (fun i (imps,v) ->
       let indp = (sp,i) in
       inductives_table := Indmap.add indp imps !inductives_table;
       Array.iteri 
	 (fun j imps ->
	    constructors_table := 
	      Constrmap.add (indp,succ j) imps !constructors_table) v)
    mibimps

let (in_mib_implicits, _) =
  let od = {
    cache_function = cache_mib_implicits;
    load_function = cache_mib_implicits;
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("MIB-IMPLICITS", od)
 
let declare_mib_implicits sp =
  let imps = compute_mib_implicits sp in
  add_anonymous_leaf (in_mib_implicits (sp,imps))

let inductive_implicits indp =
  try Indmap.find indp !inductives_table with Not_found -> No_impl

let constructor_implicits consp =
  try Constrmap.find consp !constructors_table with Not_found -> No_impl

let constructor_implicits_list constr_sp = 
  list_of_implicits (constructor_implicits constr_sp)

let inductive_implicits_list ind_sp =
  list_of_implicits (inductive_implicits ind_sp)

(*s Variables. *)

let var_table = ref Spmap.empty

let compute_var_implicits sp =
  let env = Global.env () in
  let (_,ty) = lookup_named (basename sp) env in
  auto_implicits env (body_of_type ty)

let cache_var_implicits (_,(sp,imps)) =
  var_table := Spmap.add sp imps !var_table

let (in_var_implicits, _) =
  let od = {
    cache_function = cache_var_implicits;
    load_function = cache_var_implicits;
    open_function = (fun _ -> ());
    export_function = (fun x -> Some x) }
  in
  declare_object ("VARIABLE-IMPLICITS", od)

let declare_var_implicits sp =
  let imps = compute_var_implicits sp in
  add_anonymous_leaf (in_var_implicits (sp,imps))

let implicits_of_var sp =
  list_of_implicits (try Spmap.find sp !var_table with Not_found -> No_impl)

(*s Implicits of a global reference. *)

let declare_implicits = function
  | VarRef sp -> 
      declare_var_implicits sp
  | ConstRef sp -> 
      declare_constant_implicits sp
  | IndRef ((sp,i) as indp) -> 
      let mib_imps = compute_mib_implicits sp in
      let imps = fst mib_imps.(i) in
      add_anonymous_leaf (in_inductive_implicits (indp, imps))
  | ConstructRef (((sp,i),j) as consp) -> 
      let mib_imps = compute_mib_implicits sp in
      let imps = (snd mib_imps.(i)).(j-1) in
      add_anonymous_leaf (in_constructor_implicits (consp, imps))
  | EvarRef _ -> assert false

let declare_manual_implicits r l = match r with
  | VarRef sp -> 
      add_anonymous_leaf (in_var_implicits (sp,Impl_manual l))
  | ConstRef sp ->
      add_anonymous_leaf (in_constant_implicits (sp,Impl_manual l))
  | IndRef indp ->
      add_anonymous_leaf (in_inductive_implicits (indp,Impl_manual l))
  | ConstructRef consp -> 
      add_anonymous_leaf (in_constructor_implicits (consp,Impl_manual l))
  | EvarRef _ -> 
      assert false

(*s Tests if declared implicit *)

let is_implicit_constant sp =
  try let _ = Spmap.find sp !constants_table in true with Not_found -> false

let is_implicit_inductive_definition indp =
  try let _ = Indmap.find indp !inductives_table in true 
  with Not_found -> false

let is_implicit_var sp =
  try let _ = Spmap.find sp !var_table in true with Not_found -> false

let implicits_of_global = function
  | VarRef sp -> implicits_of_var sp
  | ConstRef sp -> list_of_implicits (constant_implicits sp)
  | IndRef isp -> list_of_implicits (inductive_implicits isp)
  | ConstructRef csp ->	list_of_implicits (constructor_implicits csp)
  | EvarRef _ -> []

(*s Registration as global tables and rollback. *)

type frozen_t = bool
              * implicits Spmap.t 
              * implicits Indmap.t 
	      * implicits Constrmap.t
              * implicits Spmap.t

let init () =
  constants_table := Spmap.empty;
  inductives_table := Indmap.empty;
  constructors_table := Constrmap.empty;
  var_table := Spmap.empty

let freeze () =
  (!implicit_args, !constants_table, !inductives_table, 
   !constructors_table, !var_table)

let unfreeze (imps,ct,it,const,vt) =
  implicit_args := imps;
  constants_table := ct;
  inductives_table := it;
  constructors_table := const;
  var_table := vt

let _ = 
  Summary.declare_summary "implicits"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let rollback f x =
  let fs = freeze () in
  try f x with e -> begin unfreeze fs; raise e end

