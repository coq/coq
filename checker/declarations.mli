open Names
open Cic

val force_constr : constr_substituted -> constr
val force_lazy_constr_univs : Cic.constant_def -> Univ.ContextSet.t
val from_val : constr -> constr_substituted

val indirect_opaque_access : (DirPath.t -> int -> constr) ref
val indirect_opaque_univ_access : (DirPath.t -> int -> Univ.ContextSet.t) ref

(** Constant_body *)

val body_of_constant : constant_body -> constr option
val constant_has_body : constant_body -> bool
val is_opaque : constant_body -> bool
val opaque_univ_context : constant_body -> Univ.ContextSet.t
val constant_is_polymorphic : constant_body -> bool

(* Mutual inductives *)

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_recarg : wf_paths -> recarg
val dest_subterms : wf_paths -> wf_paths list array
val eq_recarg : recarg -> recarg -> bool
val eq_wf_paths : wf_paths -> wf_paths -> bool

val inductive_make_projections : Names.inductive -> mutual_inductive_body ->
  Names.Projection.Repr.t array option

(* Modules *)

val empty_delta_resolver : delta_resolver

(* Substitutions *)

type 'a subst_fun = substitution -> 'a -> 'a

val empty_subst : substitution
val add_mbid : MBId.t -> ModPath.t -> substitution -> substitution
val add_mp   : ModPath.t -> ModPath.t -> substitution -> substitution
val map_mbid : MBId.t -> ModPath.t -> substitution
val map_mp   : ModPath.t -> ModPath.t -> substitution
val mp_in_delta : ModPath.t -> delta_resolver -> bool
val mind_of_delta : delta_resolver -> MutInd.t -> MutInd.t

val subst_const_body : constant_body subst_fun
val subst_mind : mutual_inductive_body subst_fun
val subst_signature :  substitution -> module_signature -> module_signature
val subst_module : substitution -> module_body -> module_body

val join : substitution -> substitution -> substitution
