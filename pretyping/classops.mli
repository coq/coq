
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Evd
open Environ
open Libobject
open Declare
(*i*)

type cl_typ = 
  | CL_SORT 
  | CL_FUN 
  | CL_Var of identifier 
  | CL_SP of section_path
  | CL_IND of section_path * int

type cl_info_typ = {
  cL_STR : string;
  cL_STRE : strength;
  cL_PARAM : int }

type cte_typ = 
  | NAM_Var of identifier 
  | NAM_SP of section_path 
  | NAM_Construct of section_path * int * int

type coe_typ = cte_typ


type coe_info_typ = {
  cOE_VALUE : unsafe_judgment;
  cOE_STRE : strength;
  cOE_ISID : bool;
  cOE_PARAM : int }


type inheritance_path = int list


val cte_of_constr : constr -> cte_typ
val class_info : cl_typ -> (int * cl_info_typ)
val coercion_info : coe_typ -> (int * coe_info_typ)
val constructor_at_head : constr -> cl_typ * int
val class_of : unsafe_env -> 'c evar_map -> constr -> constr * int
val class_args_of : constr -> constr list
val inClass : (cl_typ * cl_info_typ) -> obj
val outClass : obj -> (cl_typ * cl_info_typ)
val inCoercion : (coe_typ * coe_info_typ) * cl_typ * cl_typ -> obj
val outCoercion : obj -> (coe_typ * coe_info_typ) * cl_typ * cl_typ
val lookup_path_between : (int * int) -> inheritance_path
val lookup_path_to_fun_from : int -> inheritance_path
val lookup_path_to_sort_from : int -> inheritance_path
val coe_value : int -> (unsafe_judgment * bool)
val print_graph : unit -> (int * string) Pp.ppcmd_token Stream.t
val print_classes : unit -> (int * string) Pp.ppcmd_token Stream.t
val print_coercions : unit -> (int * string) Pp.ppcmd_token Stream.t
val print_path_between : identifier -> identifier -> (int * string) ppcmd_token Stream.t
val arity_sort : constr -> int
val fully_applied : identifier -> int -> int -> unit
val stre_of_cl : cl_typ -> strength
val add_new_class : (cl_typ * string * strength * int) -> unit
val add_new_coercion_in_graph : (coe_typ * coe_info_typ) * cl_typ * cl_typ -> unit
val add_coercion_in_graph : int * int * int -> unit
