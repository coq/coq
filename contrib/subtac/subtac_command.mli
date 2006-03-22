module SPretyping :
  sig
    module Cases :
      sig
        val compile_cases :
          Util.loc ->
          (Evarutil.type_constraint ->
           Environ.env -> Rawterm.rawconstr -> Environ.unsafe_judgment) *
          Evd.evar_defs ref ->
          Evarutil.type_constraint ->
          Environ.env ->
          Rawterm.rawconstr option *
          (Rawterm.rawconstr *
           (Names.name *
            (Util.loc * Names.inductive * Names.name list) option))
          list *
          (Util.loc * Names.identifier list * Rawterm.cases_pattern list *
           Rawterm.rawconstr)
          list -> Environ.unsafe_judgment
      end
    val understand_tcc :
      Evd.evar_map ->
      Environ.env ->
      ?expected_type:Term.types -> Rawterm.rawconstr -> Evd.open_constr
    val understand_ltac :
      Evd.evar_map ->
      Environ.env ->
      Pretyping.var_map * Pretyping.unbound_ltac_var_map ->
      Pretyping.typing_constraint ->
      Rawterm.rawconstr -> Evd.evar_defs * Term.constr
    val understand :
      Evd.evar_map ->
      Environ.env ->
      ?expected_type:Term.types -> Rawterm.rawconstr -> Term.constr
    val understand_type :
      Evd.evar_map -> Environ.env -> Rawterm.rawconstr -> Term.constr
    val understand_gen :
      Pretyping.typing_constraint ->
      Evd.evar_map -> Environ.env -> Rawterm.rawconstr -> Term.constr
    val understand_judgment :
      Evd.evar_map ->
      Environ.env -> Rawterm.rawconstr -> Environ.unsafe_judgment
    val understand_judgment_tcc :
      Evd.evar_map ->
      Environ.env ->
      Rawterm.rawconstr -> Evd.evar_map * Environ.unsafe_judgment
    val pretype :
      Evarutil.type_constraint ->
      Environ.env ->
      Evd.evar_defs ref ->
      Pretyping.var_map * (Names.identifier * Names.identifier option) list ->
      Rawterm.rawconstr -> Environ.unsafe_judgment
    val pretype_type :
      Evarutil.val_constraint ->
      Environ.env ->
      Evd.evar_defs ref ->
      Pretyping.var_map * (Names.identifier * Names.identifier option) list ->
      Rawterm.rawconstr -> Environ.unsafe_type_judgment
    val pretype_gen :
      Evd.evar_defs ref ->
      Environ.env ->
      Pretyping.var_map * (Names.identifier * Names.identifier option) list ->
      Pretyping.typing_constraint -> Rawterm.rawconstr -> Term.constr
  end
val interp_gen :
  Pretyping.typing_constraint ->
  Evd.evar_defs ref ->
  Environ.env ->
  ?impls:Constrintern.full_implicits_env ->
  ?allow_soapp:bool ->
  ?ltacvars:Constrintern.ltac_sign ->
  Topconstr.constr_expr -> Evd.evar_map * Term.constr
val interp_constr :
  Evd.evar_defs ref ->
  Environ.env -> Topconstr.constr_expr -> Evd.evar_map * Term.constr
val interp_type :
  Evd.evar_defs ref ->
  Environ.env ->
  ?impls:Constrintern.full_implicits_env ->
  Topconstr.constr_expr -> Evd.evar_map * Term.constr
val interp_casted_constr :
  Evd.evar_defs ref ->
  Environ.env ->
  ?impls:Constrintern.full_implicits_env ->
  Topconstr.constr_expr -> Term.types -> Evd.evar_map * Term.constr
val interp_open_constr :
  Evd.evar_defs ref -> Environ.env -> Topconstr.constr_expr -> Term.constr
val interp_constr_judgment :
  Evd.evar_defs ref ->
  Environ.env ->
  Topconstr.constr_expr -> Evd.evar_defs * Environ.unsafe_judgment
val list_chop_hd : int -> 'a list -> 'a list * 'a * 'a list
val collect_non_rec :
  Environ.env ->
  Names.identifier list ->
  ('a * Term.types) list ->
  'b list ->
  'c list ->
  (Names.identifier * ('a * Term.types) * 'b) list *
  (Names.identifier array * ('a * Term.types) array * 'b array * 'c array)
val recursive_message : Libnames.global_reference array -> Pp.std_ppcmds
val build_recursive :
  (Topconstr.fixpoint_expr * Vernacexpr.decl_notation) list -> bool -> unit
