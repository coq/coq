open Names
open Cic

(* Environments *)

type globals = {
  env_constants : constant_body Cmap_env.t;
  env_inductives : mutual_inductive_body Mindmap_env.t;
  env_inductives_eq : KerName.t KNmap.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}
type stratification = {
  env_universes : Univ.universes;
  env_engagement : engagement;
}
type env = {
  env_globals : globals;
  env_rel_context : rel_context;
  env_stratification : stratification;
  env_imports : Cic.vodigest MPmap.t;
  env_conv_oracle : Cic.oracle;
}
val empty_env : env

(* Engagement *)
val engagement : env -> Cic.engagement
val set_engagement : Cic.engagement -> env -> env

(** Oracle *)

val set_oracle : env -> Cic.oracle -> env

(* Digests *)
val add_digest : env -> DirPath.t -> Cic.vodigest -> env
val lookup_digest : env -> DirPath.t -> Cic.vodigest

(* de Bruijn variables *)
val rel_context : env -> rel_context
val lookup_rel : int -> env -> rel_declaration
val push_rel : rel_declaration -> env -> env
val push_rel_context : rel_context -> env -> env
val push_rec_types : Name.t array * constr array * 'a -> env -> env

(* Universes *)
val universes : env -> Univ.universes
val add_constraints : Univ.constraints -> env -> env
val push_context : ?strict:bool -> Univ.universe_context -> env -> env
val push_context_set : ?strict:bool -> Univ.universe_context_set -> env -> env
val check_constraints : Univ.constraints -> env -> bool

(* Constants *)
val lookup_constant : Constant.t -> env -> Cic.constant_body
val add_constant : Constant.t -> Cic.constant_body -> env -> env
val constant_type : env -> Constant.t puniverses -> constr Univ.constrained
type const_evaluation_result = NoBody | Opaque
exception NotEvaluableConst of const_evaluation_result
val constant_value : env -> Constant.t puniverses -> constr
val evaluable_constant : Constant.t -> env -> bool

(** NB: here in the checker we check the inferred info (npars, label) *)
val lookup_projection : Projection.t -> env -> constr

(* Inductives *)
val mind_equiv : env -> inductive -> inductive -> bool

val lookup_mind :
  MutInd.t -> env -> Cic.mutual_inductive_body

val add_mind :
  MutInd.t -> Cic.mutual_inductive_body -> env -> env

(* Modules *)
val add_modtype :
  ModPath.t -> Cic.module_type_body -> env -> env
val shallow_add_module :
  ModPath.t -> Cic.module_body -> env -> env
val shallow_remove_module : ModPath.t -> env -> env
val lookup_module : ModPath.t -> env -> Cic.module_body
val lookup_modtype : ModPath.t -> env -> Cic.module_type_body
