open Names
open Cic

(* Environments *)

type globals = {
  env_constants : constant_body Cmap_env.t;
  env_inductives : mutual_inductive_body Mindmap_env.t;
  env_inductives_eq : kernel_name KNmap.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}
type stratification = {
  env_universes : Univ.universes;
  env_engagement : engagement option;
}
type env = {
  env_globals : globals;
  env_rel_context : rel_context;
  env_stratification : stratification;
  env_imports : Cic.vodigest MPmap.t;
}
val empty_env : env

(* Engagement *)
val engagement : env -> Cic.engagement option
val set_engagement : Cic.engagement -> env -> env

(* Digests *)
val add_digest : env -> DirPath.t -> Cic.vodigest -> env
val lookup_digest : env -> DirPath.t -> Cic.vodigest

(* de Bruijn variables *)
val rel_context : env -> rel_context
val lookup_rel : int -> env -> rel_declaration
val push_rel : rel_declaration -> env -> env
val push_rel_context : rel_context -> env -> env
val push_rec_types : name array * constr array * 'a -> env -> env

(* Universes *)
val universes : env -> Univ.universes
val add_constraints : Univ.constraints -> env -> env
val check_constraints : Univ.constraints -> env -> bool

(* Constants *)
val lookup_constant : constant -> env -> Cic.constant_body
val add_constant : constant -> Cic.constant_body -> env -> env
val constant_type : env -> constant puniverses -> constant_type Univ.constrained
type const_evaluation_result = NoBody | Opaque
exception NotEvaluableConst of const_evaluation_result
val constant_value : env -> constant puniverses -> constr
val evaluable_constant : constant -> env -> bool

val is_projection : constant -> env -> bool
val lookup_projection : constant -> env -> projection_body

(* Inductives *)
val mind_equiv : env -> inductive -> inductive -> bool

val lookup_mind :
  mutual_inductive -> env -> Cic.mutual_inductive_body

val add_mind :
  mutual_inductive -> Cic.mutual_inductive_body -> env -> env

(* Modules *)
val add_modtype :
  module_path -> Cic.module_type_body -> env -> env
val shallow_add_module :
  module_path -> Cic.module_body -> env -> env
val shallow_remove_module : module_path -> env -> env
val lookup_module : module_path -> env -> Cic.module_body
val lookup_modtype : module_path -> env -> Cic.module_type_body
