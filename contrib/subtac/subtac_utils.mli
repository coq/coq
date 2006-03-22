val contrib_name : string
val subtac_dir : string list
val fix_sub_module : string
val fixsub_module : string list
val init_constant : string list -> string -> Term.constr
val init_reference : string list -> string -> Libnames.global_reference
val fixsub : Term.constr lazy_t
val make_ref : string -> Libnames.reference
val well_founded_ref : Libnames.reference
val acc_ref : Libnames.reference
val acc_inv_ref : Libnames.reference
val fix_sub_ref : Libnames.reference
val lt_wf_ref : Libnames.reference
val sig_ref : Libnames.reference
val proj1_sig_ref : Libnames.reference
val proj2_sig_ref : Libnames.reference
val build_sig : unit -> Coqlib.coq_sigma_data
val sig_ : Coqlib.coq_sigma_data lazy_t
val eqind : Term.constr lazy_t
val eqind_ref : Libnames.global_reference lazy_t
val refl_equal_ref : Libnames.global_reference lazy_t
val boolind : Term.constr lazy_t
val sumboolind : Term.constr lazy_t
val natind : Term.constr lazy_t
val intind : Term.constr lazy_t
val existSind : Term.constr lazy_t
val existS : Coqlib.coq_sigma_data lazy_t
val well_founded : Term.constr lazy_t
val fix : Term.constr lazy_t
val extconstr : Term.constr -> Topconstr.constr_expr
val extsort : Term.sorts -> Topconstr.constr_expr
val my_print_constr : Environ.env -> Term.constr -> Pp.std_ppcmds
val my_print_context : Environ.env -> Pp.std_ppcmds
val my_print_env : Environ.env -> Pp.std_ppcmds
val my_print_rawconstr : Environ.env -> Rawterm.rawconstr -> Pp.std_ppcmds
val debug_level : int ref
val debug : int -> Pp.std_ppcmds -> unit
val debug_msg : int -> Pp.std_ppcmds -> Pp.std_ppcmds
val trace : Pp.std_ppcmds -> unit
val wf_relations : (Term.constr, Term.constr lazy_t) Hashtbl.t
val std_relations : unit Lazy.t
type binders = Topconstr.local_binder list
val app_opt : ('a -> 'a) option -> 'a -> 'a
val print_args : Environ.env -> Term.constr array -> Pp.std_ppcmds
val make_existential :
  Util.loc -> Environ.env -> Evd.evar_defs ref -> Term.types -> Term.constr
val make_existential_expr : Util.loc -> 'a -> 'b -> Topconstr.constr_expr
val string_of_hole_kind : Evd.hole_kind -> string
val non_instanciated_map : Environ.env -> Evd.evar_defs ref -> Evd.evar_map
val global_kind : Decl_kinds.logical_kind
val goal_kind : Decl_kinds.locality_flag * Decl_kinds.goal_object_kind
val global_fix_kind : Decl_kinds.logical_kind
val goal_fix_kind : Decl_kinds.locality_flag * Decl_kinds.goal_object_kind
