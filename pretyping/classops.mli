(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Libnames
open Nametab
open Term
open Evd
open Environ
open Declare
(*i*)

(*s This is the type of class kinds *)
type cl_typ = 
  | CL_SORT 
  | CL_FUN 
  | CL_SECVAR of variable
  | CL_CONST of constant
  | CL_IND of inductive

(* This is the type of infos for declared classes *)
type cl_info_typ = {
  cl_strength : strength;
  cl_param : int }

(* This is the type of coercion kinds *)
type coe_typ = Libnames.global_reference

(* This is the type of infos for declared coercions *)
type coe_info_typ 

(* [cl_index] is the type of class keys *)
type cl_index

(* [coe_index] is the type of coercion keys *)
type coe_index

(* This is the type of paths from a class to another *)
type inheritance_path = coe_index list

val coe_of_reference : Libnames.global_reference -> coe_typ

(*s [declare_class] adds a class to the set of declared classes *)
val declare_class : cl_typ * strength * int -> unit

(*s Access to classes infos *)
val class_info : cl_typ -> (cl_index * cl_info_typ)
val class_exists : cl_typ -> bool
val class_info_from_index : cl_index -> cl_typ * cl_info_typ

(* [find_class_type c] returns the head reference of c and its
   arguments *)
val find_class_type : constr -> cl_typ * constr list

(* raises [Not_found] if not convertible to a class *)
val class_of : env -> evar_map -> constr -> constr * cl_index

(* raises [Not_found] if not mapped to a class *)
val inductive_class_of : inductive -> cl_index

val class_args_of : constr -> constr list

val strength_of_cl : cl_typ -> strength

(*s [declare_coercion] adds a coercion in the graph of coercion paths *)
val declare_coercion : 
  coe_typ -> unsafe_judgment -> strength -> isid:bool ->
      src:cl_typ -> target:cl_typ -> params:int -> unit

(*s Access to coercions infos *)
val coercion_exists : coe_typ -> bool
val coercion_info_from_index : coe_index -> coe_typ * coe_info_typ

val coercion_value : coe_index -> (unsafe_judgment * bool)

(*s This is for printing purpose *)

(* [hide_coercion] returns the number of params to skip if the coercion must
   be hidden, [None] otherwise; it raises [Not_found] if not a coercion *)
val hide_coercion : coe_typ -> int option

val set_coercion_visibility : bool -> coe_typ -> unit
val is_coercion_visible : coe_typ -> bool

(*s Lookup functions for coercion paths *)
val lookup_path_between : cl_index * cl_index -> inheritance_path
val lookup_path_to_fun_from : cl_index -> inheritance_path
val lookup_path_to_sort_from : cl_index -> inheritance_path
val lookup_pattern_path_between :
  cl_index * cl_index -> (constructor * int) list

(*i Pour le discharge *)
type coercion = (coe_typ * coe_info_typ) * cl_typ * cl_typ

open Libobject
val inClass : (cl_typ * cl_info_typ) -> Libobject.obj
val outClass : Libobject.obj -> (cl_typ * cl_info_typ)
val inCoercion : coercion -> Libobject.obj
val outCoercion : Libobject.obj -> coercion
val coercion_strength : coe_info_typ -> strength
val coercion_identity : coe_info_typ -> bool
val coercion_params : coe_info_typ -> int
(*i*)

(*i Crade *)
open Pp
val install_path_printer : 
  ((cl_index * cl_index) * inheritance_path -> std_ppcmds) -> unit
(*i*)

(* This is for printing purpose *)
val string_of_class : cl_typ -> string
val get_coercion_value : coe_info_typ -> constr
val inheritance_graph : unit -> ((cl_index * cl_index) * inheritance_path) list
val classes : unit -> (int * (cl_typ * cl_info_typ)) list
val coercions : unit -> (int * (coe_typ * coe_info_typ)) list
