open Term
open Libnames
open Coqlib
open Environ
open Pp
open Evd
open Decl_kinds
open Topconstr
open Rawterm
open Util
open Evarutil
open Names
open Sign

val ($) : ('a -> 'b) -> 'a -> 'b
val contrib_name : string
val subtac_dir : string list
val fix_sub_module : string
val fixsub_module : string list
val init_constant : string list -> string -> constr
val init_reference : string list -> string -> global_reference
val fixsub : constr lazy_t
val well_founded_ref : global_reference lazy_t
val acc_ref : global_reference lazy_t
val acc_inv_ref : global_reference lazy_t
val fix_sub_ref : global_reference lazy_t
val fix_measure_sub_ref : global_reference lazy_t
val lt_ref : global_reference lazy_t
val lt_wf_ref : global_reference lazy_t
val refl_ref : global_reference lazy_t
val sig_ref : reference
val proj1_sig_ref : reference
val proj2_sig_ref : reference
val build_sig : unit -> coq_sigma_data
val sig_ : coq_sigma_data lazy_t

val eq_ind : constr lazy_t
val eq_rec : constr lazy_t
val eq_rect : constr lazy_t
val eq_refl : constr lazy_t

val not_ref : constr lazy_t
val and_typ : constr lazy_t

val eqdep_ind : constr lazy_t
val eqdep_rec : constr lazy_t

val jmeq_ind : constr lazy_t
val jmeq_rec : constr lazy_t
val jmeq_refl : constr lazy_t

val boolind : constr lazy_t
val sumboolind : constr lazy_t
val natind : constr lazy_t
val intind : constr lazy_t
val existSind : constr lazy_t
val existS : coq_sigma_data lazy_t
val prod : coq_sigma_data lazy_t

val well_founded : constr lazy_t
val fix : constr lazy_t
val acc : constr lazy_t
val acc_inv : constr lazy_t
val extconstr : constr -> constr_expr
val extsort : sorts -> constr_expr

val my_print_constr : env -> constr -> std_ppcmds
val my_print_constr_expr : constr_expr -> std_ppcmds
val my_print_evardefs : evar_defs -> std_ppcmds
val my_print_context : env -> std_ppcmds
val my_print_rel_context : env -> rel_context -> std_ppcmds
val my_print_named_context : env -> std_ppcmds
val my_print_env : env -> std_ppcmds
val my_print_rawconstr : env -> rawconstr -> std_ppcmds
val my_print_tycon_type : env -> type_constraint_type -> std_ppcmds


val debug : int -> std_ppcmds -> unit
val debug_msg : int -> std_ppcmds -> std_ppcmds
val trace : std_ppcmds -> unit
val wf_relations : (constr, constr lazy_t) Hashtbl.t

type binders = local_binder list
val app_opt : ('a -> 'a) option -> 'a -> 'a
val print_args : env -> constr array -> std_ppcmds
val make_existential : loc -> ?opaque:bool -> env -> evar_defs ref -> types -> constr
val make_existential_expr : loc -> 'a -> 'b -> constr_expr
val string_of_hole_kind : hole_kind -> string
val evars_of_term : evar_map -> evar_map -> constr -> evar_map
val non_instanciated_map : env -> evar_defs ref -> evar_map -> evar_map
val global_kind : logical_kind
val goal_kind : locality_flag * goal_object_kind
val global_proof_kind : logical_kind
val goal_proof_kind : locality_flag * goal_object_kind
val global_fix_kind : logical_kind
val goal_fix_kind : locality_flag * goal_object_kind

val mkSubset : name -> constr -> constr -> constr
val mkProj1 : constr -> constr -> constr -> constr
val mkProj1 : constr -> constr -> constr -> constr
val mk_ex_pi1 : constr -> constr -> constr -> constr
val mk_ex_pi1 : constr -> constr -> constr -> constr
val mk_eq : types -> constr -> constr -> types
val mk_eq_refl : types -> constr -> constr
val mk_JMeq : types -> constr-> types -> constr -> types
val mk_JMeq_refl : types -> constr -> constr
val mk_conj : types list -> types
val mk_not : types -> types

val build_dependent_sum : (identifier * types) list -> Proof_type.tactic * types
val and_tac : (identifier * 'a * constr * Proof_type.tactic) list ->  
  ((constr -> (identifier * 'a * constr * constr) list) -> Tacexpr.declaration_hook) -> unit

val destruct_ex : constr -> constr -> constr list

val id_of_name : name -> identifier

val definition_message : constant -> std_ppcmds
val recursive_message : constant array -> std_ppcmds

val print_message : std_ppcmds -> unit

val solve_by_tac : evar_info -> Tacmach.tactic -> constr

val string_of_list : string -> ('a -> string) -> 'a list -> string
val string_of_intset : Intset.t -> string

val pr_evar_defs : evar_defs -> Pp.std_ppcmds

val tactics_call : string -> Tacexpr.glob_tactic_arg list -> Tacexpr.glob_tactic_expr

val pp_list : ('a -> Pp.std_ppcmds) -> 'a list -> Pp.std_ppcmds
