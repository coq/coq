open Names
open Cic

val force_constr : constr_substituted -> constr
val from_val : constr -> constr_substituted

val indirect_opaque_access : (DirPath.t -> int -> constr) ref

(** Constant_body *)

val body_of_constant : constant_body -> constr option
val constant_has_body : constant_body -> bool
val is_opaque : constant_body -> bool

(* Mutual inductives *)

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_recarg : wf_paths -> recarg
val dest_subterms : wf_paths -> wf_paths list array

(* Modules *)

val empty_delta_resolver : delta_resolver

(* Substitutions *)

type 'a subst_fun = substitution -> 'a -> 'a

val empty_subst : substitution
val add_mbid : MBId.t -> module_path -> substitution -> substitution
val add_mp   : module_path -> module_path -> substitution -> substitution
val map_mbid : MBId.t -> module_path -> substitution
val map_mp   : module_path -> module_path -> substitution
val mp_in_delta : module_path -> delta_resolver -> bool
val mind_of_delta : delta_resolver -> mutual_inductive -> mutual_inductive

val subst_const_body : constant_body subst_fun
val subst_mind : mutual_inductive_body subst_fun
val subst_modtype : substitution -> module_type_body -> module_type_body
val subst_struct_expr :  substitution -> struct_expr_body -> struct_expr_body
val subst_structure : substitution -> structure_body -> structure_body
val subst_module : substitution -> module_body -> module_body

val join : substitution -> substitution -> substitution
