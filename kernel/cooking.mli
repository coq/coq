
(*i $Id$ i*)

open Names
open Term
open Declarations
open Environ

(*s Cooking the constants. *)

type modification_action = ABSTRACT | ERASE

type 'a modification =
  | NOT_OCCUR
  | DO_ABSTRACT of 'a * modification_action list
  | DO_REPLACE

type work_list =
    (section_path * section_path modification) list
    * (inductive_path * inductive_path modification) list
    * (constructor_path * constructor_path modification) list

type recipe = {
  d_from : section_path;
  d_abstract : identifier list;
  d_modlist : work_list }

val cook_constant : env -> recipe -> constr option * constr

(*s Utility functions used in module [Discharge]. *)

val expmod_constr : env -> work_list -> constr -> constr
val expmod_type : env -> work_list -> types -> types


