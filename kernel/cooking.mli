
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

type work_alist = (global_reference * global_reference modification) list

type recipe = {
  d_from : section_path;
  d_abstract : identifier list;
  d_modlist : work_alist }

val cook_constant : env -> recipe -> constr option * constr

(*s Utility functions used in module [Discharge]. *)

val expmod_constr : env -> work_alist -> constr -> constr
val expmod_type : env -> work_alist -> types -> types


