open Names
open Term

(* Environments *)

type globals = {
  env_constants : Declarations.constant_body Cmap_env.t;
  env_inductives : Declarations.mutual_inductive_body Mindmap_env.t;
  env_modules : Declarations.module_body MPmap.t;
  env_modtypes : Declarations.module_type_body MPmap.t}
type stratification = {
  env_universes : Univ.universes;
  env_engagement : Declarations.engagement option;
}
type env = {
  env_globals : globals;
  env_named_context : named_context;
  env_rel_context : rel_context;
  env_stratification : stratification;
  env_imports : Digest.t MPmap.t;
}
val empty_env : env

(* Engagement *)
val engagement : env -> Declarations.engagement option
val set_engagement : Declarations.engagement -> env -> env

(* Digests *)
val add_digest : env -> dir_path -> Digest.t -> env
val lookup_digest : env -> dir_path -> Digest.t

(* de Bruijn variables *)
val rel_context : env -> rel_context
val lookup_rel : int -> env -> rel_declaration
val push_rel : rel_declaration -> env -> env
val push_rel_context : rel_context -> env -> env
val push_rec_types : name array * constr array * 'a -> env -> env

(* Named variables *)
val named_context : env -> named_context
val push_named : named_declaration -> env -> env
val lookup_named : identifier -> env -> named_declaration
val named_type : identifier -> env -> constr

(* Universes *)
val universes : env -> Univ.universes
val add_constraints : Univ.constraints -> env -> env

(* Constants *)
val lookup_constant : constant -> env -> Declarations.constant_body
val add_constant : constant -> Declarations.constant_body -> env -> env
val constant_type : env -> constant -> Declarations.constant_type
type const_evaluation_result = NoBody | Opaque
exception NotEvaluableConst of const_evaluation_result
val constant_value : env -> constant -> constr
val constant_opt_value : env -> constant -> constr option
val evaluable_constant : constant -> env -> bool

(* Inductives *)
val lookup_mind :
  mutual_inductive -> env -> Declarations.mutual_inductive_body

val add_mind :
  mutual_inductive -> Declarations.mutual_inductive_body -> env -> env

(* Modules *)
val add_modtype :
  module_path -> Declarations.module_type_body -> env -> env
val shallow_add_module :
  module_path -> Declarations.module_body -> env -> env
val lookup_module : module_path -> env -> Declarations.module_body
val lookup_modtype : module_path -> env -> Declarations.module_type_body
