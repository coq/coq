(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Decl_kinds
open Term
open Evd
open Environ
open Nametab
open Mod_subst
(*i*)

(*s This is the type of class kinds *)
type cl_typ = 
  | CL_SORT 
  | CL_FUN 
  | CL_SECVAR of variable
  | CL_CONST of constant
  | CL_IND of inductive

val subst_cl_typ : substitution -> cl_typ -> cl_typ

(* This is the type of infos for declared classes *)
type cl_info_typ = {
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

(*s [declare_coercion] adds a coercion in the graph of coercion paths *)
val declare_coercion : 
  coe_typ -> strength -> isid:bool ->
      src:cl_typ -> target:cl_typ -> params:int -> unit

(*s Access to coercions infos *)
val coercion_exists : coe_typ -> bool

val coercion_value : coe_index -> (unsafe_judgment * bool)

(*s Lookup functions for coercion paths *)
val lookup_path_between : cl_index * cl_index -> inheritance_path
val lookup_path_to_fun_from : cl_index -> inheritance_path
val lookup_path_to_sort_from : cl_index -> inheritance_path
val lookup_pattern_path_between :
  cl_index * cl_index -> (constructor * int) list

(*i Crade *)
open Pp
val install_path_printer : 
  ((cl_index * cl_index) * inheritance_path -> std_ppcmds) -> unit
(*i*)

(*s This is for printing purpose *)
val string_of_class : cl_typ -> string
val pr_class : cl_typ -> std_ppcmds
val get_coercion_value : coe_index -> constr
val inheritance_graph : unit -> ((cl_index * cl_index) * inheritance_path) list
val classes : unit -> cl_typ list
val coercions : unit -> coe_index list

(* [hide_coercion] returns the number of params to skip if the coercion must
   be hidden, [None] otherwise; it raises [Not_found] if not a coercion *)
val hide_coercion : coe_typ -> int option
