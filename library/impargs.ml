
(* $Id$ *)

open Names
open Generic
open Term
open Reduction
open Constant
open Inductive
open Typing

type implicits =
  | Impl_auto of int list
  | Impl_manual of int list
  | No_impl

let implicit_args = ref false

let auto_implicits ty =
  if !implicit_args then
    let genv = unsafe_env_of_env (Global.env()) in
    Impl_auto (poly_args genv Evd.empty ty)
  else
    No_impl

(* Constants. *)

let constants_table = ref Spmap.empty

let declare_constant_implicits sp =
  let cb = Global.lookup_constant sp in
  let imps = auto_implicits cb.const_type.body in
  constants_table := Spmap.add sp imps !constants_table

let declare_constant_manual_implicits sp imps =
  constants_table := Spmap.add sp (Impl_manual imps) !constants_table

let constant_implicits sp =
  Spmap.find sp !constants_table

(* Inductives and constructors. Their implicit arguments are stored
   in an array, indexed by the inductive number, of pairs $(i,v)$ where
   $i$ are the implicit arguments of the inductive and $v$ the array of 
   implicit arguments of the constructors. *)

let inductives_table = ref Spmap.empty

let declare_inductive_implicits sp =
  let mib = Global.lookup_mind sp in
  let imps_one_inductive mip =
    (auto_implicits mip.mind_arity.body,
     let (_,lc) = decomp_all_DLAMV_name mip.mind_lc in
     Array.map auto_implicits lc)
  in
  let imps = Array.map imps_one_inductive mib.mind_packets in
  inductives_table := Spmap.add sp imps !inductives_table
    
let inductive_implicits (sp,i) =
  let imps = Spmap.find sp !inductives_table in
  fst imps.(i)

let constructor_implicits ((sp,i),j) =
  let imps = Spmap.find sp !inductives_table in
  (snd imps.(i)).(pred j)

(* Registration as global tables and roolback. *)

type frozen = implicits Spmap.t

let init () =
  constants_table := Spmap.empty

let freeze () =
  !constants_table

let unfreeze ct =
  constants_table := ct

let _ = 
  Summary.declare_summary "implicits"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let rollback f x =
  let fs = freeze () in
  try f x with e -> begin unfreeze fs; raise e end
