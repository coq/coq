type ct_AST =
    CT_coerce_ID_OR_INT_to_AST of ct_ID_OR_INT
  | CT_coerce_ID_OR_STRING_to_AST of ct_ID_OR_STRING
  | CT_coerce_SINGLE_OPTION_VALUE_to_AST of ct_SINGLE_OPTION_VALUE
  | CT_astnode of ct_ID * ct_AST_LIST
  | CT_astpath of ct_ID_LIST
  | CT_astslam of ct_ID_OPT * ct_AST
and ct_AST_LIST =
    CT_ast_list of ct_AST list
and ct_BINARY =
    CT_binary of int
and ct_BINDER =
    CT_coerce_DEF_to_BINDER of ct_DEF
  | CT_binder of ct_ID_OPT_NE_LIST * ct_FORMULA
  | CT_binder_coercion of ct_ID_OPT_NE_LIST * ct_FORMULA
and ct_BINDER_LIST =
    CT_binder_list of ct_BINDER list
and ct_BINDER_NE_LIST =
    CT_binder_ne_list of ct_BINDER * ct_BINDER list
and ct_BINDING =
    CT_binding of ct_ID_OR_INT * ct_FORMULA
and ct_BINDING_LIST =
    CT_binding_list of ct_BINDING list
and t_BOOL =
    CT_false
  | CT_true
and ct_CASE =
    CT_case of string
and ct_CLAUSE =
    CT_clause of ct_HYP_LOCATION_LIST_OR_STAR * ct_STAR_OPT
and ct_COERCION_OPT =
    CT_coerce_NONE_to_COERCION_OPT of ct_NONE
  | CT_coercion_atm
and ct_COFIXTAC =
    CT_cofixtac of ct_ID * ct_FORMULA
and ct_COFIX_REC =
    CT_cofix_rec of ct_ID * ct_BINDER_LIST * ct_FORMULA * ct_FORMULA
and ct_COFIX_REC_LIST =
    CT_cofix_rec_list of ct_COFIX_REC * ct_COFIX_REC list
and ct_COFIX_TAC_LIST =
    CT_cofix_tac_list of ct_COFIXTAC list
and ct_COMMAND =
    CT_coerce_COMMAND_LIST_to_COMMAND of ct_COMMAND_LIST
  | CT_coerce_EVAL_CMD_to_COMMAND of ct_EVAL_CMD
  | CT_coerce_SECTION_BEGIN_to_COMMAND of ct_SECTION_BEGIN
  | CT_coerce_THEOREM_GOAL_to_COMMAND of ct_THEOREM_GOAL
  | CT_abort of ct_ID_OPT_OR_ALL
  | CT_abstraction of ct_ID * ct_FORMULA * ct_INT_LIST
  | CT_add_field of ct_FORMULA * ct_FORMULA * ct_FORMULA * ct_FORMULA_OPT
  | CT_add_natural_feature of ct_NATURAL_FEATURE * ct_ID
  | CT_addpath of ct_STRING * ct_ID_OPT
  | CT_arguments_scope of ct_ID * ct_ID_OPT_LIST
  | CT_bind_scope of ct_ID * ct_ID_NE_LIST
  | CT_cd of ct_STRING_OPT
  | CT_check of ct_FORMULA
  | CT_class of ct_ID
  | CT_close_scope of ct_ID
  | CT_coercion of ct_LOCAL_OPT * ct_IDENTITY_OPT * ct_ID * ct_ID * ct_ID
  | CT_cofix_decl of ct_COFIX_REC_LIST
  | CT_compile_module of ct_VERBOSE_OPT * ct_ID * ct_STRING_OPT
  | CT_declare_module of ct_ID * ct_MODULE_BINDER_LIST * ct_MODULE_TYPE_CHECK * ct_MODULE_EXPR
  | CT_define_notation of ct_STRING * ct_FORMULA * ct_MODIFIER_LIST * ct_ID_OPT
  | CT_definition of ct_DEFN * ct_ID * ct_BINDER_LIST * ct_DEF_BODY * ct_FORMULA_OPT
  | CT_delim_scope of ct_ID * ct_ID
  | CT_delpath of ct_STRING
  | CT_derive_depinversion of ct_INV_TYPE * ct_ID * ct_FORMULA * ct_SORT_TYPE
  | CT_derive_inversion of ct_INV_TYPE * ct_INT_OPT * ct_ID * ct_ID
  | CT_derive_inversion_with of ct_INV_TYPE * ct_ID * ct_FORMULA * ct_SORT_TYPE
  | CT_explain_proof of ct_INT_LIST
  | CT_explain_prooftree of ct_INT_LIST
  | CT_export_id of ct_ID_NE_LIST
  | CT_extract_to_file of ct_STRING * ct_ID_NE_LIST
  | CT_extraction of ct_ID_OPT
  | CT_fix_decl of ct_FIX_REC_LIST
  | CT_focus of ct_INT_OPT
  | CT_go of ct_INT_OR_LOCN
  | CT_guarded
  | CT_hint_destruct of ct_ID * ct_INT * ct_DESTRUCT_LOCATION * ct_FORMULA * ct_TACTIC_COM * ct_ID_LIST
  | CT_hint_extern of ct_INT * ct_FORMULA * ct_TACTIC_COM * ct_ID_LIST
  | CT_hintrewrite of ct_ORIENTATION * ct_FORMULA_NE_LIST * ct_ID * ct_TACTIC_COM
  | CT_hints of ct_ID * ct_ID_NE_LIST * ct_ID_LIST
  | CT_hints_immediate of ct_FORMULA_NE_LIST * ct_ID_LIST
  | CT_hints_resolve of ct_FORMULA_NE_LIST * ct_ID_LIST
  | CT_hyp_search_pattern of ct_FORMULA * ct_IN_OR_OUT_MODULES
  | CT_implicits of ct_ID * ct_ID_LIST_OPT
  | CT_import_id of ct_ID_NE_LIST
  | CT_ind_scheme of ct_SCHEME_SPEC_LIST
  | CT_infix of ct_STRING * ct_ID * ct_MODIFIER_LIST * ct_ID_OPT
  | CT_inline of ct_ID_NE_LIST
  | CT_inspect of ct_INT
  | CT_kill_node of ct_INT
  | CT_load of ct_VERBOSE_OPT * ct_ID_OR_STRING
  | CT_local_close_scope of ct_ID
  | CT_local_define_notation of ct_STRING * ct_FORMULA * ct_MODIFIER_LIST * ct_ID_OPT
  | CT_local_hint_destruct of ct_ID * ct_INT * ct_DESTRUCT_LOCATION * ct_FORMULA * ct_TACTIC_COM * ct_ID_LIST
  | CT_local_hint_extern of ct_INT * ct_FORMULA * ct_TACTIC_COM * ct_ID_LIST
  | CT_local_hints of ct_ID * ct_ID_NE_LIST * ct_ID_LIST
  | CT_local_hints_immediate of ct_FORMULA_NE_LIST * ct_ID_LIST
  | CT_local_hints_resolve of ct_FORMULA_NE_LIST * ct_ID_LIST
  | CT_local_infix of ct_STRING * ct_ID * ct_MODIFIER_LIST * ct_ID_OPT
  | CT_local_open_scope of ct_ID
  | CT_local_reserve_notation of ct_STRING * ct_MODIFIER_LIST
  | CT_locate of ct_ID
  | CT_locate_file of ct_STRING
  | CT_locate_lib of ct_ID
  | CT_locate_notation of ct_STRING
  | CT_mind_decl of ct_CO_IND * ct_IND_SPEC_LIST
  | CT_ml_add_path of ct_STRING
  | CT_ml_declare_modules of ct_STRING_NE_LIST
  | CT_ml_print_modules
  | CT_ml_print_path
  | CT_module of ct_ID * ct_MODULE_BINDER_LIST * ct_MODULE_TYPE_CHECK * ct_MODULE_EXPR
  | CT_module_type_decl of ct_ID * ct_MODULE_BINDER_LIST * ct_MODULE_TYPE_OPT
  | CT_no_inline of ct_ID_NE_LIST
  | CT_omega_flag of ct_OMEGA_MODE * ct_OMEGA_FEATURE
  | CT_open_scope of ct_ID
  | CT_print
  | CT_print_about of ct_ID
  | CT_print_all
  | CT_print_classes
  | CT_print_ltac of ct_ID
  | CT_print_coercions
  | CT_print_grammar of ct_GRAMMAR
  | CT_print_graph
  | CT_print_hint of ct_ID_OPT
  | CT_print_hintdb of ct_ID_OR_STAR
  | CT_print_rewrite_hintdb of ct_ID
  | CT_print_id of ct_ID
  | CT_print_implicit of ct_ID
  | CT_print_loadpath
  | CT_print_module of ct_ID
  | CT_print_module_type of ct_ID
  | CT_print_modules
  | CT_print_natural of ct_ID
  | CT_print_natural_feature of ct_NATURAL_FEATURE
  | CT_print_opaqueid of ct_ID
  | CT_print_path of ct_ID * ct_ID
  | CT_print_proof of ct_ID
  | CT_print_setoids
  | CT_print_scope of ct_ID
  | CT_print_scopes
  | CT_print_section of ct_ID
  | CT_print_states
  | CT_print_tables
  | CT_print_universes of ct_STRING_OPT
  | CT_print_visibility of ct_ID_OPT
  | CT_proof of ct_FORMULA
  | CT_proof_no_op
  | CT_proof_with of ct_TACTIC_COM
  | CT_pwd
  | CT_quit
  | CT_read_module of ct_ID
  | CT_rec_ml_add_path of ct_STRING
  | CT_recaddpath of ct_STRING * ct_ID_OPT
  | CT_record of ct_COERCION_OPT * ct_ID * ct_BINDER_LIST * ct_FORMULA * ct_ID_OPT * ct_RECCONSTR_LIST
  | CT_remove_natural_feature of ct_NATURAL_FEATURE * ct_ID
  | CT_require of ct_IMPEXP * ct_SPEC_OPT * ct_ID_NE_LIST_OR_STRING
  | CT_reserve of ct_ID_NE_LIST * ct_FORMULA
  | CT_reserve_notation of ct_STRING * ct_MODIFIER_LIST
  | CT_reset of ct_ID
  | CT_reset_section of ct_ID
  | CT_restart
  | CT_restore_state of ct_ID
  | CT_resume of ct_ID_OPT
  | CT_save of ct_THM_OPT * ct_ID_OPT
  | CT_scomments of ct_SCOMMENT_CONTENT_LIST
  | CT_search of ct_ID * ct_IN_OR_OUT_MODULES
  | CT_search_about of ct_ID_OR_STRING_NE_LIST * ct_IN_OR_OUT_MODULES
  | CT_search_pattern of ct_FORMULA * ct_IN_OR_OUT_MODULES
  | CT_search_rewrite of ct_FORMULA * ct_IN_OR_OUT_MODULES
  | CT_section_end of ct_ID
  | CT_section_struct of ct_SECTION_BEGIN * ct_SECTION_BODY * ct_COMMAND
  | CT_set_natural of ct_ID
  | CT_set_natural_default
  | CT_set_option of ct_TABLE
  | CT_set_option_value of ct_TABLE * ct_SINGLE_OPTION_VALUE
  | CT_set_option_value2 of ct_TABLE * ct_ID_OR_STRING_NE_LIST
  | CT_sethyp of ct_INT
  | CT_setundo of ct_INT
  | CT_show_existentials
  | CT_show_goal of ct_INT_OPT
  | CT_show_implicit of ct_INT
  | CT_show_intro
  | CT_show_intros
  | CT_show_node
  | CT_show_proof
  | CT_show_proofs
  | CT_show_script
  | CT_show_tree
  | CT_solve of ct_INT * ct_TACTIC_COM * ct_DOTDOT_OPT
  | CT_strategy of ct_LEVEL_LIST
  | CT_suspend
  | CT_syntax_macro of ct_ID * ct_FORMULA * ct_INT_OPT
  | CT_tactic_definition of ct_TAC_DEF_NE_LIST
  | CT_test_natural_feature of ct_NATURAL_FEATURE * ct_ID
  | CT_theorem_struct of ct_THEOREM_GOAL * ct_PROOF_SCRIPT
  | CT_time of ct_COMMAND
  | CT_undo of ct_INT_OPT
  | CT_unfocus
  | CT_unset_option of ct_TABLE
  | CT_unsethyp
  | CT_unsetundo
  | CT_user_vernac of ct_ID * ct_VARG_LIST
  | CT_variable of ct_VAR * ct_BINDER_NE_LIST
  | CT_write_module of ct_ID * ct_STRING_OPT
and ct_LEVEL_LIST =
    CT_level_list of (ct_LEVEL * ct_ID_LIST) list
and ct_LEVEL =
    CT_Opaque
  | CT_Level of ct_INT
  | CT_Expand
and ct_COMMAND_LIST =
    CT_command_list of ct_COMMAND * ct_COMMAND list
and ct_COMMENT =
    CT_comment of string
and ct_COMMENT_S =
    CT_comment_s of ct_COMMENT list
and ct_CONSTR =
    CT_constr of ct_ID * ct_FORMULA
  | CT_constr_coercion of ct_ID * ct_FORMULA
and ct_CONSTR_LIST =
    CT_constr_list of ct_CONSTR list
and ct_CONTEXT_HYP_LIST =
    CT_context_hyp_list of ct_PREMISE_PATTERN list
and ct_CONTEXT_PATTERN =
    CT_coerce_FORMULA_to_CONTEXT_PATTERN of ct_FORMULA
  | CT_context of ct_ID_OPT * ct_FORMULA
and ct_CONTEXT_RULE =
    CT_context_rule of ct_CONTEXT_HYP_LIST * ct_CONTEXT_PATTERN * ct_TACTIC_COM
  | CT_def_context_rule of ct_TACTIC_COM
and ct_CONVERSION_FLAG =
    CT_beta
  | CT_delta
  | CT_evar
  | CT_iota
  | CT_zeta
and ct_CONVERSION_FLAG_LIST =
    CT_conversion_flag_list of ct_CONVERSION_FLAG list
and ct_CONV_SET =
    CT_unf of ct_ID list
  | CT_unfbut of ct_ID list
and ct_CO_IND =
    CT_co_ind of string
and ct_DECL_NOTATION_OPT =
    CT_coerce_NONE_to_DECL_NOTATION_OPT of ct_NONE
  | CT_decl_notation of ct_STRING * ct_FORMULA * ct_ID_OPT
and ct_DEF =
    CT_def of ct_ID_OPT * ct_FORMULA
and ct_DEFN =
    CT_defn of string
and ct_DEFN_OR_THM =
    CT_coerce_DEFN_to_DEFN_OR_THM of ct_DEFN
  | CT_coerce_THM_to_DEFN_OR_THM of ct_THM
and ct_DEF_BODY =
    CT_coerce_CONTEXT_PATTERN_to_DEF_BODY of ct_CONTEXT_PATTERN
  | CT_coerce_EVAL_CMD_to_DEF_BODY of ct_EVAL_CMD
  | CT_type_of of ct_FORMULA
and ct_DEF_BODY_OPT =
    CT_coerce_DEF_BODY_to_DEF_BODY_OPT of ct_DEF_BODY
  | CT_coerce_FORMULA_OPT_to_DEF_BODY_OPT of ct_FORMULA_OPT
and ct_DEP =
    CT_dep of string
and ct_DESTRUCTING =
    CT_coerce_NONE_to_DESTRUCTING of ct_NONE
  | CT_destructing
and ct_DESTRUCT_LOCATION =
    CT_conclusion_location
  | CT_discardable_hypothesis
  | CT_hypothesis_location
and ct_DOTDOT_OPT =
    CT_coerce_NONE_to_DOTDOT_OPT of ct_NONE
  | CT_dotdot
and ct_EQN =
    CT_eqn of ct_MATCH_PATTERN_NE_LIST * ct_FORMULA
and ct_EQN_LIST =
    CT_eqn_list of ct_EQN list
and ct_EVAL_CMD =
    CT_eval of ct_INT_OPT * ct_RED_COM * ct_FORMULA
and ct_FIXTAC =
    CT_fixtac of ct_ID * ct_INT * ct_FORMULA
and ct_FIX_BINDER =
    CT_coerce_FIX_REC_to_FIX_BINDER of ct_FIX_REC
  | CT_fix_binder of ct_ID * ct_INT * ct_FORMULA * ct_FORMULA
and ct_FIX_BINDER_LIST =
    CT_fix_binder_list of ct_FIX_BINDER * ct_FIX_BINDER list
and ct_FIX_REC =
    CT_fix_rec of ct_ID * ct_BINDER_NE_LIST * ct_ID_OPT *
      ct_FORMULA * ct_FORMULA
and ct_FIX_REC_LIST =
    CT_fix_rec_list of ct_FIX_REC * ct_FIX_REC list
and ct_FIX_TAC_LIST =
    CT_fix_tac_list of ct_FIXTAC list
and ct_FORMULA =
    CT_coerce_BINARY_to_FORMULA of ct_BINARY
  | CT_coerce_ID_to_FORMULA of ct_ID
  | CT_coerce_NUM_to_FORMULA of ct_NUM
  | CT_coerce_SORT_TYPE_to_FORMULA of ct_SORT_TYPE
  | CT_coerce_TYPED_FORMULA_to_FORMULA of ct_TYPED_FORMULA
  | CT_appc of ct_FORMULA * ct_FORMULA_NE_LIST
  | CT_arrowc of ct_FORMULA * ct_FORMULA
  | CT_bang of ct_FORMULA
  | CT_cases of ct_MATCHED_FORMULA_NE_LIST * ct_FORMULA_OPT * ct_EQN_LIST
  | CT_cofixc of ct_ID * ct_COFIX_REC_LIST
  | CT_elimc of ct_CASE * ct_FORMULA_OPT * ct_FORMULA * ct_FORMULA_LIST
  | CT_existvarc
  | CT_fixc of ct_ID * ct_FIX_BINDER_LIST
  | CT_if of ct_FORMULA * ct_RETURN_INFO * ct_FORMULA * ct_FORMULA
  | CT_inductive_let of ct_FORMULA_OPT * ct_ID_OPT_NE_LIST * ct_FORMULA * ct_FORMULA
  | CT_labelled_arg of ct_ID * ct_FORMULA
  | CT_lambdac of ct_BINDER_NE_LIST * ct_FORMULA
  | CT_let_tuple of ct_ID_OPT_NE_LIST * ct_RETURN_INFO * ct_FORMULA * ct_FORMULA
  | CT_letin of ct_DEF * ct_FORMULA
  | CT_notation of ct_STRING * ct_FORMULA_LIST
  | CT_num_encapsulator of ct_NUM_TYPE * ct_FORMULA
  | CT_prodc of ct_BINDER_NE_LIST * ct_FORMULA
  | CT_proj of ct_FORMULA * ct_FORMULA_NE_LIST
and ct_FORMULA_LIST =
    CT_formula_list of ct_FORMULA list
and ct_FORMULA_NE_LIST =
    CT_formula_ne_list of ct_FORMULA * ct_FORMULA list
and ct_FORMULA_OPT =
    CT_coerce_FORMULA_to_FORMULA_OPT of ct_FORMULA
  | CT_coerce_ID_OPT_to_FORMULA_OPT of ct_ID_OPT
and ct_FORMULA_OR_INT =
    CT_coerce_FORMULA_to_FORMULA_OR_INT of ct_FORMULA
  | CT_coerce_ID_OR_INT_to_FORMULA_OR_INT of ct_ID_OR_INT
and ct_GRAMMAR =
    CT_grammar_none
and ct_HYP_LOCATION =
    CT_coerce_UNFOLD_to_HYP_LOCATION of ct_UNFOLD
  | CT_intype of ct_ID * ct_INT_LIST
  | CT_invalue of ct_ID * ct_INT_LIST
and ct_HYP_LOCATION_LIST_OR_STAR =
    CT_coerce_STAR_to_HYP_LOCATION_LIST_OR_STAR of ct_STAR
  | CT_hyp_location_list of ct_HYP_LOCATION list
and ct_ID =
    CT_ident of string
  | CT_metac of ct_INT
  | CT_metaid of string
and ct_IDENTITY_OPT =
    CT_coerce_NONE_to_IDENTITY_OPT of ct_NONE
  | CT_identity
and ct_ID_LIST =
    CT_id_list of ct_ID list
and ct_ID_LIST_LIST =
    CT_id_list_list of ct_ID_LIST list
and ct_ID_LIST_OPT =
    CT_coerce_ID_LIST_to_ID_LIST_OPT of ct_ID_LIST
  | CT_coerce_NONE_to_ID_LIST_OPT of ct_NONE
and ct_ID_NE_LIST =
    CT_id_ne_list of ct_ID * ct_ID list
and ct_ID_NE_LIST_OR_STAR =
    CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR of ct_ID_NE_LIST
  | CT_coerce_STAR_to_ID_NE_LIST_OR_STAR of ct_STAR
and ct_ID_NE_LIST_OR_STRING =
    CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STRING of ct_ID_NE_LIST
  | CT_coerce_STRING_to_ID_NE_LIST_OR_STRING of ct_STRING
and ct_ID_OPT =
    CT_coerce_ID_to_ID_OPT of ct_ID
  | CT_coerce_NONE_to_ID_OPT of ct_NONE
and ct_ID_OPT_LIST =
    CT_id_opt_list of ct_ID_OPT list
and ct_ID_OPT_NE_LIST =
    CT_id_opt_ne_list of ct_ID_OPT * ct_ID_OPT list
and ct_ID_OPT_OR_ALL =
    CT_coerce_ID_OPT_to_ID_OPT_OR_ALL of ct_ID_OPT
  | CT_all
and ct_ID_OR_INT =
    CT_coerce_ID_to_ID_OR_INT of ct_ID
  | CT_coerce_INT_to_ID_OR_INT of ct_INT
and ct_ID_OR_INT_OPT =
    CT_coerce_ID_OPT_to_ID_OR_INT_OPT of ct_ID_OPT
  | CT_coerce_ID_OR_INT_to_ID_OR_INT_OPT of ct_ID_OR_INT
  | CT_coerce_INT_OPT_to_ID_OR_INT_OPT of ct_INT_OPT
and ct_ID_OR_STAR =
    CT_coerce_ID_to_ID_OR_STAR of ct_ID
  | CT_coerce_STAR_to_ID_OR_STAR of ct_STAR
and ct_ID_OR_STRING =
    CT_coerce_ID_to_ID_OR_STRING of ct_ID
  | CT_coerce_STRING_to_ID_OR_STRING of ct_STRING
and ct_ID_OR_STRING_NE_LIST =
    CT_id_or_string_ne_list of ct_ID_OR_STRING * ct_ID_OR_STRING list
and ct_IMPEXP =
    CT_coerce_NONE_to_IMPEXP of ct_NONE
  | CT_export
  | CT_import
and ct_IND_SPEC =
    CT_ind_spec of ct_ID * ct_BINDER_LIST * ct_FORMULA * ct_CONSTR_LIST * ct_DECL_NOTATION_OPT
and ct_IND_SPEC_LIST =
    CT_ind_spec_list of ct_IND_SPEC list
and ct_INT =
    CT_int of int
and ct_INTRO_PATT =
    CT_coerce_ID_to_INTRO_PATT of ct_ID
  | CT_disj_pattern of ct_INTRO_PATT_LIST * ct_INTRO_PATT_LIST list
and ct_INTRO_PATT_LIST =
    CT_intro_patt_list of ct_INTRO_PATT list
and ct_INTRO_PATT_OPT =
    CT_coerce_ID_OPT_to_INTRO_PATT_OPT of ct_ID_OPT
  | CT_coerce_INTRO_PATT_to_INTRO_PATT_OPT of ct_INTRO_PATT
and ct_INT_LIST =
    CT_int_list of ct_INT list
and ct_INT_NE_LIST =
    CT_int_ne_list of ct_INT * ct_INT list
and ct_INT_OPT =
    CT_coerce_INT_to_INT_OPT of ct_INT
  | CT_coerce_NONE_to_INT_OPT of ct_NONE
and ct_INT_OR_LOCN =
    CT_coerce_INT_to_INT_OR_LOCN of ct_INT
  | CT_coerce_LOCN_to_INT_OR_LOCN of ct_LOCN
and ct_INT_OR_NEXT =
    CT_coerce_INT_to_INT_OR_NEXT of ct_INT
  | CT_next_level
and ct_INV_TYPE =
    CT_inv_clear
  | CT_inv_regular
  | CT_inv_simple
and ct_IN_OR_OUT_MODULES =
    CT_coerce_NONE_to_IN_OR_OUT_MODULES of ct_NONE
  | CT_in_modules of ct_ID_NE_LIST
  | CT_out_modules of ct_ID_NE_LIST
and ct_LET_CLAUSE =
    CT_let_clause of ct_ID * ct_TACTIC_OPT * ct_LET_VALUE
and ct_LET_CLAUSES =
    CT_let_clauses of ct_LET_CLAUSE * ct_LET_CLAUSE list
and ct_LET_VALUE =
    CT_coerce_DEF_BODY_to_LET_VALUE of ct_DEF_BODY
  | CT_coerce_TACTIC_COM_to_LET_VALUE of ct_TACTIC_COM
and ct_LOCAL_OPT =
    CT_coerce_NONE_to_LOCAL_OPT of ct_NONE
  | CT_local
and ct_LOCN =
    CT_locn of string
and ct_MATCHED_FORMULA =
    CT_coerce_FORMULA_to_MATCHED_FORMULA of ct_FORMULA
  | CT_formula_as of ct_FORMULA * ct_ID_OPT
  | CT_formula_as_in of ct_FORMULA * ct_ID_OPT * ct_FORMULA
  | CT_formula_in of ct_FORMULA * ct_FORMULA
and ct_MATCHED_FORMULA_NE_LIST =
    CT_matched_formula_ne_list of ct_MATCHED_FORMULA * ct_MATCHED_FORMULA list
and ct_MATCH_PATTERN =
    CT_coerce_ID_OPT_to_MATCH_PATTERN of ct_ID_OPT
  | CT_coerce_NUM_to_MATCH_PATTERN of ct_NUM
  | CT_pattern_app of ct_MATCH_PATTERN * ct_MATCH_PATTERN_NE_LIST
  | CT_pattern_as of ct_MATCH_PATTERN * ct_ID_OPT
  | CT_pattern_delimitors of ct_NUM_TYPE * ct_MATCH_PATTERN
  | CT_pattern_notation of ct_STRING * ct_MATCH_PATTERN_LIST
and ct_MATCH_PATTERN_LIST =
    CT_match_pattern_list of ct_MATCH_PATTERN list
and ct_MATCH_PATTERN_NE_LIST =
    CT_match_pattern_ne_list of ct_MATCH_PATTERN * ct_MATCH_PATTERN list
and ct_MATCH_TAC_RULE =
    CT_match_tac_rule of ct_CONTEXT_PATTERN * ct_LET_VALUE
and ct_MATCH_TAC_RULES =
    CT_match_tac_rules of ct_MATCH_TAC_RULE * ct_MATCH_TAC_RULE list
and ct_MODIFIER =
    CT_entry_type of ct_ID * ct_ID
  | CT_format of ct_STRING
  | CT_lefta
  | CT_nona
  | CT_only_parsing
  | CT_righta
  | CT_set_item_level of ct_ID_NE_LIST * ct_INT_OR_NEXT
  | CT_set_level of ct_INT
and ct_MODIFIER_LIST =
    CT_modifier_list of ct_MODIFIER list
and ct_MODULE_BINDER =
    CT_module_binder of ct_ID_NE_LIST * ct_MODULE_TYPE
and ct_MODULE_BINDER_LIST =
    CT_module_binder_list of ct_MODULE_BINDER list
and ct_MODULE_EXPR =
    CT_coerce_ID_OPT_to_MODULE_EXPR of ct_ID_OPT
  | CT_module_app of ct_MODULE_EXPR * ct_MODULE_EXPR
and ct_MODULE_TYPE =
    CT_coerce_ID_to_MODULE_TYPE of ct_ID
  | CT_module_type_with_def of ct_MODULE_TYPE * ct_ID_LIST * ct_FORMULA
  | CT_module_type_with_mod of ct_MODULE_TYPE * ct_ID_LIST * ct_ID
and ct_MODULE_TYPE_CHECK =
    CT_coerce_MODULE_TYPE_OPT_to_MODULE_TYPE_CHECK of ct_MODULE_TYPE_OPT
  | CT_only_check of ct_MODULE_TYPE
and ct_MODULE_TYPE_OPT =
    CT_coerce_ID_OPT_to_MODULE_TYPE_OPT of ct_ID_OPT
  | CT_coerce_MODULE_TYPE_to_MODULE_TYPE_OPT of ct_MODULE_TYPE
and ct_NATURAL_FEATURE =
    CT_contractible
  | CT_implicit
  | CT_nat_transparent
and ct_NONE =
    CT_none
and ct_NUM =
    CT_int_encapsulator of string
and ct_NUM_TYPE =
    CT_num_type of string
and ct_OMEGA_FEATURE =
    CT_coerce_STRING_to_OMEGA_FEATURE of ct_STRING
  | CT_flag_action
  | CT_flag_system
  | CT_flag_time
and ct_OMEGA_MODE =
    CT_set
  | CT_switch
  | CT_unset
and ct_ORIENTATION =
    CT_lr
  | CT_rl
and ct_PATTERN =
    CT_pattern_occ of ct_INT_LIST * ct_FORMULA
and ct_PATTERN_NE_LIST =
    CT_pattern_ne_list of ct_PATTERN * ct_PATTERN list
and ct_PATTERN_OPT =
    CT_coerce_NONE_to_PATTERN_OPT of ct_NONE
  | CT_coerce_PATTERN_to_PATTERN_OPT of ct_PATTERN
and ct_PREMISE =
    CT_coerce_TYPED_FORMULA_to_PREMISE of ct_TYPED_FORMULA
  | CT_eval_result of ct_FORMULA * ct_FORMULA * ct_FORMULA
  | CT_premise of ct_ID * ct_FORMULA
and ct_PREMISES_LIST =
    CT_premises_list of ct_PREMISE list
and ct_PREMISE_PATTERN =
    CT_premise_pattern of ct_ID_OPT * ct_CONTEXT_PATTERN
and ct_PROOF_SCRIPT =
    CT_proof_script of ct_COMMAND list
and ct_RECCONSTR =
    CT_defrecconstr of ct_ID_OPT * ct_FORMULA * ct_FORMULA_OPT
  | CT_defrecconstr_coercion of ct_ID_OPT * ct_FORMULA * ct_FORMULA_OPT
  | CT_recconstr of ct_ID_OPT * ct_FORMULA
  | CT_recconstr_coercion of ct_ID_OPT * ct_FORMULA
and ct_RECCONSTR_LIST =
    CT_recconstr_list of ct_RECCONSTR list
and ct_REC_TACTIC_FUN =
    CT_rec_tactic_fun of ct_ID * ct_ID_OPT_NE_LIST * ct_TACTIC_COM
and ct_REC_TACTIC_FUN_LIST =
    CT_rec_tactic_fun_list of ct_REC_TACTIC_FUN * ct_REC_TACTIC_FUN list
and ct_RED_COM =
    CT_cbv of ct_CONVERSION_FLAG_LIST * ct_CONV_SET
  | CT_fold of ct_FORMULA_LIST
  | CT_hnf
  | CT_lazy of ct_CONVERSION_FLAG_LIST * ct_CONV_SET
  | CT_pattern of ct_PATTERN_NE_LIST
  | CT_red
  | CT_cbvvm
  | CT_simpl of ct_PATTERN_OPT
  | CT_unfold of ct_UNFOLD_NE_LIST
and ct_RETURN_INFO =
    CT_coerce_NONE_to_RETURN_INFO of ct_NONE
  | CT_as_and_return of ct_ID_OPT * ct_FORMULA
  | CT_return of ct_FORMULA
and ct_RULE =
    CT_rule of ct_PREMISES_LIST * ct_FORMULA
and ct_RULE_LIST =
    CT_rule_list of ct_RULE list
and ct_SCHEME_SPEC =
    CT_scheme_spec of ct_ID * ct_DEP * ct_FORMULA * ct_SORT_TYPE
and ct_SCHEME_SPEC_LIST =
    CT_scheme_spec_list of ct_SCHEME_SPEC * ct_SCHEME_SPEC list
and ct_SCOMMENT_CONTENT =
    CT_coerce_FORMULA_to_SCOMMENT_CONTENT of ct_FORMULA
  | CT_coerce_ID_OR_STRING_to_SCOMMENT_CONTENT of ct_ID_OR_STRING
and ct_SCOMMENT_CONTENT_LIST =
    CT_scomment_content_list of ct_SCOMMENT_CONTENT list
and ct_SECTION_BEGIN =
    CT_section of ct_ID
and ct_SECTION_BODY =
    CT_section_body of ct_COMMAND list
and ct_SIGNED_INT =
    CT_coerce_INT_to_SIGNED_INT of ct_INT
  | CT_minus of ct_INT
and ct_SIGNED_INT_LIST =
    CT_signed_int_list of ct_SIGNED_INT list
and ct_SINGLE_OPTION_VALUE =
    CT_coerce_INT_to_SINGLE_OPTION_VALUE of ct_INT
  | CT_coerce_STRING_to_SINGLE_OPTION_VALUE of ct_STRING
and ct_SORT_TYPE =
    CT_sortc of string
and ct_SPEC_LIST =
    CT_coerce_BINDING_LIST_to_SPEC_LIST of ct_BINDING_LIST
  | CT_coerce_FORMULA_LIST_to_SPEC_LIST of ct_FORMULA_LIST
and ct_SPEC_OPT =
    CT_coerce_NONE_to_SPEC_OPT of ct_NONE
  | CT_spec
and ct_STAR =
    CT_star
and ct_STAR_OPT =
    CT_coerce_NONE_to_STAR_OPT of ct_NONE
  | CT_coerce_STAR_to_STAR_OPT of ct_STAR
and ct_STRING =
    CT_string of string
and ct_STRING_NE_LIST =
    CT_string_ne_list of ct_STRING * ct_STRING list
and ct_STRING_OPT =
    CT_coerce_NONE_to_STRING_OPT of ct_NONE
  | CT_coerce_STRING_to_STRING_OPT of ct_STRING
and ct_TABLE =
    CT_coerce_ID_to_TABLE of ct_ID
  | CT_table of ct_ID * ct_ID
and ct_TACTIC_ARG =
    CT_coerce_EVAL_CMD_to_TACTIC_ARG of ct_EVAL_CMD
  | CT_coerce_FORMULA_OR_INT_to_TACTIC_ARG of ct_FORMULA_OR_INT
  | CT_coerce_TACTIC_COM_to_TACTIC_ARG of ct_TACTIC_COM
  | CT_coerce_TERM_CHANGE_to_TACTIC_ARG of ct_TERM_CHANGE
  | CT_void
and ct_TACTIC_ARG_LIST =
    CT_tactic_arg_list of ct_TACTIC_ARG * ct_TACTIC_ARG list
and ct_TACTIC_COM =
    CT_abstract of ct_ID_OPT * ct_TACTIC_COM
  | CT_absurd of ct_FORMULA
  | CT_any_constructor of ct_TACTIC_OPT
  | CT_apply of ct_FORMULA * ct_SPEC_LIST
  | CT_assert of ct_ID_OPT * ct_FORMULA
  | CT_assumption
  | CT_auto of ct_INT_OPT
  | CT_auto_with of ct_INT_OPT * ct_ID_NE_LIST_OR_STAR
  | CT_autorewrite of ct_ID_NE_LIST * ct_TACTIC_OPT
  | CT_autotdb of ct_INT_OPT
  | CT_case_type of ct_FORMULA
  | CT_casetac of ct_FORMULA * ct_SPEC_LIST
  | CT_cdhyp of ct_ID
  | CT_change of ct_FORMULA * ct_CLAUSE
  | CT_change_local of ct_PATTERN * ct_FORMULA * ct_CLAUSE
  | CT_clear of ct_ID_NE_LIST
  | CT_clear_body of ct_ID_NE_LIST
  | CT_cofixtactic of ct_ID_OPT * ct_COFIX_TAC_LIST
  | CT_condrewrite_lr of ct_TACTIC_COM * ct_FORMULA * ct_SPEC_LIST * ct_ID_OPT
  | CT_condrewrite_rl of ct_TACTIC_COM * ct_FORMULA * ct_SPEC_LIST * ct_ID_OPT
  | CT_constructor of ct_INT * ct_SPEC_LIST
  | CT_contradiction
  | CT_contradiction_thm of ct_FORMULA * ct_SPEC_LIST
  | CT_cut of ct_FORMULA
  | CT_cutrewrite_lr of ct_FORMULA * ct_ID_OPT
  | CT_cutrewrite_rl of ct_FORMULA * ct_ID_OPT
  | CT_dauto of ct_INT_OPT * ct_INT_OPT
  | CT_dconcl
  | CT_decompose_list of ct_ID_NE_LIST * ct_FORMULA
  | CT_decompose_record of ct_FORMULA
  | CT_decompose_sum of ct_FORMULA
  | CT_depinversion of ct_INV_TYPE * ct_ID_OR_INT * ct_INTRO_PATT_OPT * ct_FORMULA_OPT
  | CT_deprewrite_lr of ct_ID
  | CT_deprewrite_rl of ct_ID
  | CT_destruct of ct_ID_OR_INT
  | CT_dhyp of ct_ID
  | CT_discriminate_eq of ct_ID_OR_INT_OPT
  | CT_do of ct_ID_OR_INT * ct_TACTIC_COM
  | CT_eapply of ct_FORMULA * ct_SPEC_LIST
  | CT_eauto of ct_ID_OR_INT_OPT * ct_ID_OR_INT_OPT
  | CT_eauto_with of ct_ID_OR_INT_OPT * ct_ID_OR_INT_OPT * ct_ID_NE_LIST_OR_STAR
  | CT_elim of ct_FORMULA * ct_SPEC_LIST * ct_USING
  | CT_elim_type of ct_FORMULA
  | CT_exact of ct_FORMULA
  | CT_exact_no_check of ct_FORMULA
  | CT_vm_cast_no_check of ct_FORMULA
  | CT_exists of ct_SPEC_LIST
  | CT_fail of ct_ID_OR_INT * ct_STRING_OPT
  | CT_first of ct_TACTIC_COM * ct_TACTIC_COM list
  | CT_firstorder of ct_TACTIC_OPT
  | CT_firstorder_using of ct_TACTIC_OPT * ct_ID_NE_LIST
  | CT_firstorder_with of ct_TACTIC_OPT * ct_ID_NE_LIST
  | CT_fixtactic of ct_ID_OPT * ct_INT * ct_FIX_TAC_LIST
  | CT_formula_marker of ct_FORMULA
  | CT_fresh of ct_STRING_OPT
  | CT_generalize of ct_FORMULA_NE_LIST
  | CT_generalize_dependent of ct_FORMULA
  | CT_idtac of ct_STRING_OPT
  | CT_induction of ct_ID_OR_INT
  | CT_info of ct_TACTIC_COM
  | CT_injection_eq of ct_ID_OR_INT_OPT
  | CT_instantiate of ct_INT * ct_FORMULA * ct_CLAUSE
  | CT_intro of ct_ID_OPT
  | CT_intro_after of ct_ID_OPT * ct_ID
  | CT_intros of ct_INTRO_PATT_LIST
  | CT_intros_until of ct_ID_OR_INT
  | CT_inversion of ct_INV_TYPE * ct_ID_OR_INT * ct_INTRO_PATT_OPT * ct_ID_LIST
  | CT_left of ct_SPEC_LIST
  | CT_let_ltac of ct_LET_CLAUSES * ct_LET_VALUE
  | CT_lettac of ct_ID_OPT * ct_FORMULA * ct_CLAUSE
  | CT_match_context of ct_CONTEXT_RULE * ct_CONTEXT_RULE list
  | CT_match_context_reverse of ct_CONTEXT_RULE * ct_CONTEXT_RULE list
  | CT_match_tac of ct_TACTIC_COM * ct_MATCH_TAC_RULES
  | CT_move_after of ct_ID * ct_ID
  | CT_new_destruct of ct_FORMULA_OR_INT list * ct_USING * ct_INTRO_PATT_OPT
  | CT_new_induction of ct_FORMULA_OR_INT list * ct_USING * ct_INTRO_PATT_OPT
  | CT_omega
  | CT_orelse of ct_TACTIC_COM * ct_TACTIC_COM
  | CT_parallel of ct_TACTIC_COM * ct_TACTIC_COM list
  | CT_pose of ct_ID_OPT * ct_FORMULA
  | CT_progress of ct_TACTIC_COM
  | CT_prolog of ct_FORMULA_LIST * ct_INT
  | CT_rec_tactic_in of ct_REC_TACTIC_FUN_LIST * ct_TACTIC_COM
  | CT_reduce of ct_RED_COM * ct_CLAUSE
  | CT_refine of ct_FORMULA
  | CT_reflexivity
  | CT_rename of ct_ID * ct_ID
  | CT_repeat of ct_TACTIC_COM
  | CT_replace_with of ct_FORMULA * ct_FORMULA * ct_CLAUSE * ct_TACTIC_OPT
  | CT_rewrite_lr of ct_FORMULA * ct_SPEC_LIST * ct_CLAUSE
  | CT_rewrite_rl of ct_FORMULA * ct_SPEC_LIST * ct_CLAUSE
  | CT_right of ct_SPEC_LIST
  | CT_ring of ct_FORMULA_LIST
  | CT_simple_user_tac of ct_ID * ct_TACTIC_ARG_LIST
  | CT_simplify_eq of ct_ID_OR_INT_OPT
  | CT_specialize of ct_INT_OPT * ct_FORMULA * ct_SPEC_LIST
  | CT_split of ct_SPEC_LIST
  | CT_subst of ct_ID_LIST
  | CT_superauto of ct_INT_OPT * ct_ID_LIST * ct_DESTRUCTING * ct_USINGTDB
  | CT_symmetry of ct_CLAUSE
  | CT_tac_double of ct_ID_OR_INT * ct_ID_OR_INT
  | CT_tacsolve of ct_TACTIC_COM * ct_TACTIC_COM list
  | CT_tactic_fun of ct_ID_OPT_NE_LIST * ct_TACTIC_COM
  | CT_then of ct_TACTIC_COM * ct_TACTIC_COM list
  | CT_transitivity of ct_FORMULA
  | CT_trivial
  | CT_trivial_with of ct_ID_NE_LIST_OR_STAR
  | CT_truecut of ct_ID_OPT * ct_FORMULA
  | CT_try of ct_TACTIC_COM
  | CT_use of ct_FORMULA
  | CT_use_inversion of ct_ID_OR_INT * ct_FORMULA * ct_ID_LIST
  | CT_user_tac of ct_ID * ct_TARG_LIST
and ct_TACTIC_OPT =
    CT_coerce_NONE_to_TACTIC_OPT of ct_NONE
  | CT_coerce_TACTIC_COM_to_TACTIC_OPT of ct_TACTIC_COM
and ct_TAC_DEF =
    CT_tac_def of ct_ID * ct_TACTIC_COM
and ct_TAC_DEF_NE_LIST =
    CT_tac_def_ne_list of ct_TAC_DEF * ct_TAC_DEF list
and ct_TARG =
    CT_coerce_BINDING_to_TARG of ct_BINDING
  | CT_coerce_COFIXTAC_to_TARG of ct_COFIXTAC
  | CT_coerce_FIXTAC_to_TARG of ct_FIXTAC
  | CT_coerce_FORMULA_OR_INT_to_TARG of ct_FORMULA_OR_INT
  | CT_coerce_PATTERN_to_TARG of ct_PATTERN
  | CT_coerce_SCOMMENT_CONTENT_to_TARG of ct_SCOMMENT_CONTENT
  | CT_coerce_SIGNED_INT_LIST_to_TARG of ct_SIGNED_INT_LIST
  | CT_coerce_SINGLE_OPTION_VALUE_to_TARG of ct_SINGLE_OPTION_VALUE
  | CT_coerce_SPEC_LIST_to_TARG of ct_SPEC_LIST
  | CT_coerce_TACTIC_COM_to_TARG of ct_TACTIC_COM
  | CT_coerce_TARG_LIST_to_TARG of ct_TARG_LIST
  | CT_coerce_UNFOLD_to_TARG of ct_UNFOLD
  | CT_coerce_UNFOLD_NE_LIST_to_TARG of ct_UNFOLD_NE_LIST
and ct_TARG_LIST =
    CT_targ_list of ct_TARG list
and ct_TERM_CHANGE =
    CT_check_term of ct_FORMULA
  | CT_inst_term of ct_ID * ct_FORMULA
and ct_TEXT =
    CT_coerce_ID_to_TEXT of ct_ID
  | CT_text_formula of ct_FORMULA
  | CT_text_h of ct_TEXT list
  | CT_text_hv of ct_TEXT list
  | CT_text_op of ct_TEXT list
  | CT_text_path of ct_SIGNED_INT_LIST
  | CT_text_v of ct_TEXT list
and ct_THEOREM_GOAL =
    CT_goal of ct_FORMULA
  | CT_theorem_goal of ct_DEFN_OR_THM * ct_ID * ct_BINDER_LIST * ct_FORMULA
and ct_THM =
    CT_thm of string
and ct_THM_OPT =
    CT_coerce_NONE_to_THM_OPT of ct_NONE
  | CT_coerce_THM_to_THM_OPT of ct_THM
and ct_TYPED_FORMULA =
    CT_typed_formula of ct_FORMULA * ct_FORMULA
and ct_UNFOLD =
    CT_coerce_ID_to_UNFOLD of ct_ID
  | CT_unfold_occ of ct_ID * ct_INT_NE_LIST
and ct_UNFOLD_NE_LIST =
    CT_unfold_ne_list of ct_UNFOLD * ct_UNFOLD list
and ct_USING =
    CT_coerce_NONE_to_USING of ct_NONE
  | CT_using of ct_FORMULA * ct_SPEC_LIST
and ct_USINGTDB =
    CT_coerce_NONE_to_USINGTDB of ct_NONE
  | CT_usingtdb
and ct_VAR =
    CT_var of string
and ct_VARG =
    CT_coerce_AST_to_VARG of ct_AST
  | CT_coerce_AST_LIST_to_VARG of ct_AST_LIST
  | CT_coerce_BINDER_to_VARG of ct_BINDER
  | CT_coerce_BINDER_LIST_to_VARG of ct_BINDER_LIST
  | CT_coerce_BINDER_NE_LIST_to_VARG of ct_BINDER_NE_LIST
  | CT_coerce_FORMULA_LIST_to_VARG of ct_FORMULA_LIST
  | CT_coerce_FORMULA_OPT_to_VARG of ct_FORMULA_OPT
  | CT_coerce_FORMULA_OR_INT_to_VARG of ct_FORMULA_OR_INT
  | CT_coerce_ID_OPT_OR_ALL_to_VARG of ct_ID_OPT_OR_ALL
  | CT_coerce_ID_OR_INT_OPT_to_VARG of ct_ID_OR_INT_OPT
  | CT_coerce_INT_LIST_to_VARG of ct_INT_LIST
  | CT_coerce_SCOMMENT_CONTENT_to_VARG of ct_SCOMMENT_CONTENT
  | CT_coerce_STRING_OPT_to_VARG of ct_STRING_OPT
  | CT_coerce_TACTIC_OPT_to_VARG of ct_TACTIC_OPT
  | CT_coerce_VARG_LIST_to_VARG of ct_VARG_LIST
and ct_VARG_LIST =
    CT_varg_list of ct_VARG list
and ct_VERBOSE_OPT =
    CT_coerce_NONE_to_VERBOSE_OPT of ct_NONE
  | CT_verbose
;;
