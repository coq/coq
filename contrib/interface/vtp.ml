open Ascent;;
open Pp;;

(* LEM: This is actually generated automatically *)

let fNODE s n =
    (str "n\n") ++
    (str ("vernac$" ^ s)) ++
    (str "\n") ++
    (int n) ++
    (str "\n");;

let fATOM s1 =
    (str "a\n") ++
    (str ("vernac$" ^ s1)) ++
    (str "\n");;

let f_atom_string = str;;
let f_atom_int = int;;
let rec fAST = function
| CT_coerce_ID_OR_INT_to_AST x -> fID_OR_INT x
| CT_coerce_ID_OR_STRING_to_AST x -> fID_OR_STRING x
| CT_coerce_SINGLE_OPTION_VALUE_to_AST x -> fSINGLE_OPTION_VALUE x
| CT_astnode(x1, x2) ->
   fID x1 ++
   fAST_LIST x2 ++
   fNODE "astnode" 2
| CT_astpath(x1) ->
   fID_LIST x1 ++
   fNODE "astpath" 1
| CT_astslam(x1, x2) ->
   fID_OPT x1 ++
   fAST x2 ++
   fNODE "astslam" 2
and fAST_LIST = function
| CT_ast_list l ->
   (List.fold_left (++) (mt()) (List.map fAST l)) ++
   fNODE "ast_list" (List.length l)
and fBINARY = function
| CT_binary x -> fATOM "binary" ++
   (f_atom_int x) ++
   str "\n"
and fBINDER = function
| CT_coerce_DEF_to_BINDER x -> fDEF x
| CT_binder(x1, x2) ->
   fID_OPT_NE_LIST x1 ++
   fFORMULA x2 ++
   fNODE "binder" 2
| CT_binder_coercion(x1, x2) ->
   fID_OPT_NE_LIST x1 ++
   fFORMULA x2 ++
   fNODE "binder_coercion" 2
and fBINDER_LIST = function
| CT_binder_list l ->
   (List.fold_left (++) (mt()) (List.map fBINDER l)) ++
   fNODE "binder_list" (List.length l)
and fBINDER_NE_LIST = function
| CT_binder_ne_list(x,l) ->
   fBINDER x ++
   (List.fold_left (++) (mt()) (List.map fBINDER l)) ++
   fNODE "binder_ne_list" (1 + (List.length l))
and fBINDING = function
| CT_binding(x1, x2) ->
   fID_OR_INT x1 ++
   fFORMULA x2 ++
   fNODE "binding" 2
and fBINDING_LIST = function
| CT_binding_list l ->
   (List.fold_left (++) (mt()) (List.map fBINDING l)) ++
   fNODE "binding_list" (List.length l)
and fBOOL = function
| CT_false -> fNODE "false" 0
| CT_true -> fNODE "true" 0
and fCASE = function
| CT_case x -> fATOM "case" ++
   (f_atom_string x) ++
   str "\n"
and fCLAUSE = function
| CT_clause(x1, x2) ->
   fHYP_LOCATION_LIST_OR_STAR x1 ++
   fSTAR_OPT x2 ++
   fNODE "clause" 2
and fCOERCION_OPT = function
| CT_coerce_NONE_to_COERCION_OPT x -> fNONE x
| CT_coercion_atm -> fNODE "coercion_atm" 0
and fCOFIXTAC = function
| CT_cofixtac(x1, x2) ->
   fID x1 ++
   fFORMULA x2 ++
   fNODE "cofixtac" 2
and fCOFIX_REC = function
| CT_cofix_rec(x1, x2, x3, x4) ->
   fID x1 ++
   fBINDER_LIST x2 ++
   fFORMULA x3 ++
   fFORMULA x4 ++
   fNODE "cofix_rec" 4
and fCOFIX_REC_LIST = function
| CT_cofix_rec_list(x,l) ->
   fCOFIX_REC x ++
   (List.fold_left (++) (mt()) (List.map fCOFIX_REC l)) ++
   fNODE "cofix_rec_list" (1 + (List.length l))
and fCOFIX_TAC_LIST = function
| CT_cofix_tac_list l ->
   (List.fold_left (++) (mt()) (List.map fCOFIXTAC l)) ++
   fNODE "cofix_tac_list" (List.length l)
and fCOMMAND = function
| CT_coerce_COMMAND_LIST_to_COMMAND x -> fCOMMAND_LIST x
| CT_coerce_EVAL_CMD_to_COMMAND x -> fEVAL_CMD x
| CT_coerce_SECTION_BEGIN_to_COMMAND x -> fSECTION_BEGIN x
| CT_coerce_THEOREM_GOAL_to_COMMAND x -> fTHEOREM_GOAL x
| CT_abort(x1) ->
   fID_OPT_OR_ALL x1 ++
   fNODE "abort" 1
| CT_abstraction(x1, x2, x3) ->
   fID x1 ++
   fFORMULA x2 ++
   fINT_LIST x3 ++
   fNODE "abstraction" 3
| CT_add_field(x1, x2, x3, x4) ->
   fFORMULA x1 ++
   fFORMULA x2 ++
   fFORMULA x3 ++
   fFORMULA_OPT x4 ++
   fNODE "add_field" 4
| CT_add_natural_feature(x1, x2) ->
   fNATURAL_FEATURE x1 ++
   fID x2 ++
   fNODE "add_natural_feature" 2
| CT_addpath(x1, x2) ->
   fSTRING x1 ++
   fID_OPT x2 ++
   fNODE "addpath" 2
| CT_arguments_scope(x1, x2) ->
   fID x1 ++
   fID_OPT_LIST x2 ++
   fNODE "arguments_scope" 2
| CT_bind_scope(x1, x2) ->
   fID x1 ++
   fID_NE_LIST x2 ++
   fNODE "bind_scope" 2
| CT_cd(x1) ->
   fSTRING_OPT x1 ++
   fNODE "cd" 1
| CT_check(x1) ->
   fFORMULA x1 ++
   fNODE "check" 1
| CT_class(x1) ->
   fID x1 ++
   fNODE "class" 1
| CT_close_scope(x1) ->
   fID x1 ++
   fNODE "close_scope" 1
| CT_coercion(x1, x2, x3, x4, x5) ->
   fLOCAL_OPT x1 ++
   fIDENTITY_OPT x2 ++
   fID x3 ++
   fID x4 ++
   fID x5 ++
   fNODE "coercion" 5
| CT_cofix_decl(x1) ->
   fCOFIX_REC_LIST x1 ++
   fNODE "cofix_decl" 1
| CT_compile_module(x1, x2, x3) ->
   fVERBOSE_OPT x1 ++
   fID x2 ++
   fSTRING_OPT x3 ++
   fNODE "compile_module" 3
| CT_declare_module(x1, x2, x3, x4) ->
   fID x1 ++
   fMODULE_BINDER_LIST x2 ++
   fMODULE_TYPE_CHECK x3 ++
   fMODULE_EXPR x4 ++
   fNODE "declare_module" 4
| CT_define_notation(x1, x2, x3, x4) ->
   fSTRING x1 ++
   fFORMULA x2 ++
   fMODIFIER_LIST x3 ++
   fID_OPT x4 ++
   fNODE "define_notation" 4
| CT_definition(x1, x2, x3, x4, x5) ->
   fDEFN x1 ++
   fID x2 ++
   fBINDER_LIST x3 ++
   fDEF_BODY x4 ++
   fFORMULA_OPT x5 ++
   fNODE "definition" 5
| CT_delim_scope(x1, x2) ->
   fID x1 ++
   fID x2 ++
   fNODE "delim_scope" 2
| CT_delpath(x1) ->
   fSTRING x1 ++
   fNODE "delpath" 1
| CT_derive_depinversion(x1, x2, x3, x4) ->
   fINV_TYPE x1 ++
   fID x2 ++
   fFORMULA x3 ++
   fSORT_TYPE x4 ++
   fNODE "derive_depinversion" 4
| CT_derive_inversion(x1, x2, x3, x4) ->
   fINV_TYPE x1 ++
   fINT_OPT x2 ++
   fID x3 ++
   fID x4 ++
   fNODE "derive_inversion" 4
| CT_derive_inversion_with(x1, x2, x3, x4) ->
   fINV_TYPE x1 ++
   fID x2 ++
   fFORMULA x3 ++
   fSORT_TYPE x4 ++
   fNODE "derive_inversion_with" 4
| CT_explain_proof(x1) ->
   fINT_LIST x1 ++
   fNODE "explain_proof" 1
| CT_explain_prooftree(x1) ->
   fINT_LIST x1 ++
   fNODE "explain_prooftree" 1
| CT_export_id(x1) ->
   fID_NE_LIST x1 ++
   fNODE "export_id" 1
| CT_extract_to_file(x1, x2) ->
   fSTRING x1 ++
   fID_NE_LIST x2 ++
   fNODE "extract_to_file" 2
| CT_extraction(x1) ->
   fID_OPT x1 ++
   fNODE "extraction" 1
| CT_fix_decl(x1) ->
   fFIX_REC_LIST x1 ++
   fNODE "fix_decl" 1
| CT_focus(x1) ->
   fINT_OPT x1 ++
   fNODE "focus" 1
| CT_go(x1) ->
   fINT_OR_LOCN x1 ++
   fNODE "go" 1
| CT_guarded -> fNODE "guarded" 0
| CT_hint_destruct(x1, x2, x3, x4, x5, x6) ->
   fID x1 ++
   fINT x2 ++
   fDESTRUCT_LOCATION x3 ++
   fFORMULA x4 ++
   fTACTIC_COM x5 ++
   fID_LIST x6 ++
   fNODE "hint_destruct" 6
| CT_hint_extern(x1, x2, x3, x4) ->
   fINT x1 ++
   fFORMULA_OPT x2 ++
   fTACTIC_COM x3 ++
   fID_LIST x4 ++
   fNODE "hint_extern" 4
| CT_hintrewrite(x1, x2, x3, x4) ->
   fORIENTATION x1 ++
   fFORMULA_NE_LIST x2 ++
   fID x3 ++
   fTACTIC_COM x4 ++
   fNODE "hintrewrite" 4
| CT_hints(x1, x2, x3) ->
   fID x1 ++
   fID_NE_LIST x2 ++
   fID_LIST x3 ++
   fNODE "hints" 3
| CT_hints_immediate(x1, x2) ->
   fFORMULA_NE_LIST x1 ++
   fID_LIST x2 ++
   fNODE "hints_immediate" 2
| CT_hints_resolve(x1, x2) ->
   fFORMULA_NE_LIST x1 ++
   fID_LIST x2 ++
   fNODE "hints_resolve" 2
| CT_hyp_search_pattern(x1, x2) ->
   fFORMULA x1 ++
   fIN_OR_OUT_MODULES x2 ++
   fNODE "hyp_search_pattern" 2
| CT_implicits(x1, x2) ->
   fID x1 ++
   fID_LIST_OPT x2 ++
   fNODE "implicits" 2
| CT_import_id(x1) ->
   fID_NE_LIST x1 ++
   fNODE "import_id" 1
| CT_ind_scheme(x1) ->
   fSCHEME_SPEC_LIST x1 ++
   fNODE "ind_scheme" 1
| CT_infix(x1, x2, x3, x4) ->
   fSTRING x1 ++
   fID x2 ++
   fMODIFIER_LIST x3 ++
   fID_OPT x4 ++
   fNODE "infix" 4
| CT_inline(x1) ->
   fID_NE_LIST x1 ++
   fNODE "inline" 1
| CT_inspect(x1) ->
   fINT x1 ++
   fNODE "inspect" 1
| CT_kill_node(x1) ->
   fINT x1 ++
   fNODE "kill_node" 1
| CT_load(x1, x2) ->
   fVERBOSE_OPT x1 ++
   fID_OR_STRING x2 ++
   fNODE "load" 2
| CT_local_close_scope(x1) ->
   fID x1 ++
   fNODE "local_close_scope" 1
| CT_local_define_notation(x1, x2, x3, x4) ->
   fSTRING x1 ++
   fFORMULA x2 ++
   fMODIFIER_LIST x3 ++
   fID_OPT x4 ++
   fNODE "local_define_notation" 4
| CT_local_hint_destruct(x1, x2, x3, x4, x5, x6) ->
   fID x1 ++
   fINT x2 ++
   fDESTRUCT_LOCATION x3 ++
   fFORMULA x4 ++
   fTACTIC_COM x5 ++
   fID_LIST x6 ++
   fNODE "local_hint_destruct" 6
| CT_local_hint_extern(x1, x2, x3, x4) ->
   fINT x1 ++
   fFORMULA x2 ++
   fTACTIC_COM x3 ++
   fID_LIST x4 ++
   fNODE "local_hint_extern" 4
| CT_local_hints(x1, x2, x3) ->
   fID x1 ++
   fID_NE_LIST x2 ++
   fID_LIST x3 ++
   fNODE "local_hints" 3
| CT_local_hints_immediate(x1, x2) ->
   fFORMULA_NE_LIST x1 ++
   fID_LIST x2 ++
   fNODE "local_hints_immediate" 2
| CT_local_hints_resolve(x1, x2) ->
   fFORMULA_NE_LIST x1 ++
   fID_LIST x2 ++
   fNODE "local_hints_resolve" 2
| CT_local_infix(x1, x2, x3, x4) ->
   fSTRING x1 ++
   fID x2 ++
   fMODIFIER_LIST x3 ++
   fID_OPT x4 ++
   fNODE "local_infix" 4
| CT_local_open_scope(x1) ->
   fID x1 ++
   fNODE "local_open_scope" 1
| CT_local_reserve_notation(x1, x2) ->
   fSTRING x1 ++
   fMODIFIER_LIST x2 ++
   fNODE "local_reserve_notation" 2
| CT_locate(x1) ->
   fID x1 ++
   fNODE "locate" 1
| CT_locate_file(x1) ->
   fSTRING x1 ++
   fNODE "locate_file" 1
| CT_locate_lib(x1) ->
   fID x1 ++
   fNODE "locate_lib" 1
| CT_locate_notation(x1) ->
   fSTRING x1 ++
   fNODE "locate_notation" 1
| CT_mind_decl(x1, x2) ->
   fCO_IND x1 ++
   fIND_SPEC_LIST x2 ++
   fNODE "mind_decl" 2
| CT_ml_add_path(x1) ->
   fSTRING x1 ++
   fNODE "ml_add_path" 1
| CT_ml_declare_modules(x1) ->
   fSTRING_NE_LIST x1 ++
   fNODE "ml_declare_modules" 1
| CT_ml_print_modules -> fNODE "ml_print_modules" 0
| CT_ml_print_path -> fNODE "ml_print_path" 0
| CT_module(x1, x2, x3, x4) ->
   fID x1 ++
   fMODULE_BINDER_LIST x2 ++
   fMODULE_TYPE_CHECK x3 ++
   fMODULE_EXPR x4 ++
   fNODE "module" 4
| CT_module_type_decl(x1, x2, x3) ->
   fID x1 ++
   fMODULE_BINDER_LIST x2 ++
   fMODULE_TYPE_OPT x3 ++
   fNODE "module_type_decl" 3
| CT_no_inline(x1) ->
   fID_NE_LIST x1 ++
   fNODE "no_inline" 1
| CT_omega_flag(x1, x2) ->
   fOMEGA_MODE x1 ++
   fOMEGA_FEATURE x2 ++
   fNODE "omega_flag" 2
| CT_open_scope(x1) ->
   fID x1 ++
   fNODE "open_scope" 1
| CT_print -> fNODE "print" 0
| CT_print_about(x1) ->
   fID x1 ++
   fNODE "print_about" 1
| CT_print_all -> fNODE "print_all" 0
| CT_print_classes -> fNODE "print_classes" 0
| CT_print_ltac id ->
   fID id ++
   fNODE "print_ltac" 1
| CT_print_coercions -> fNODE "print_coercions" 0
| CT_print_grammar(x1) ->
   fGRAMMAR x1 ++
   fNODE "print_grammar" 1
| CT_print_graph -> fNODE "print_graph" 0
| CT_print_hint(x1) ->
   fID_OPT x1 ++
   fNODE "print_hint" 1
| CT_print_hintdb(x1) ->
   fID_OR_STAR x1 ++
   fNODE "print_hintdb" 1
| CT_print_rewrite_hintdb(x1) ->
   fID x1 ++
   fNODE "print_rewrite_hintdb" 1
| CT_print_id(x1) ->
   fID x1 ++
   fNODE "print_id" 1
| CT_print_implicit(x1) ->
   fID x1 ++
   fNODE "print_implicit" 1
| CT_print_loadpath -> fNODE "print_loadpath" 0
| CT_print_module(x1) ->
   fID x1 ++
   fNODE "print_module" 1
| CT_print_module_type(x1) ->
   fID x1 ++
   fNODE "print_module_type" 1
| CT_print_modules -> fNODE "print_modules" 0
| CT_print_natural(x1) ->
   fID x1 ++
   fNODE "print_natural" 1
| CT_print_natural_feature(x1) ->
   fNATURAL_FEATURE x1 ++
   fNODE "print_natural_feature" 1
| CT_print_opaqueid(x1) ->
   fID x1 ++
   fNODE "print_opaqueid" 1
| CT_print_path(x1, x2) ->
   fID x1 ++
   fID x2 ++
   fNODE "print_path" 2
| CT_print_proof(x1) ->
   fID x1 ++
   fNODE "print_proof" 1
| CT_print_scope(x1) ->
   fID x1 ++
   fNODE "print_scope" 1
| CT_print_setoids -> fNODE "print_setoids" 0
| CT_print_scopes -> fNODE "print_scopes" 0
| CT_print_section(x1) ->
   fID x1 ++
   fNODE "print_section" 1
| CT_print_states -> fNODE "print_states" 0
| CT_print_tables -> fNODE "print_tables" 0
| CT_print_universes(x1) ->
   fSTRING_OPT x1 ++
   fNODE "print_universes" 1
| CT_print_visibility(x1) ->
   fID_OPT x1 ++
   fNODE "print_visibility" 1
| CT_proof(x1) ->
   fFORMULA x1 ++
   fNODE "proof" 1
| CT_proof_no_op -> fNODE "proof_no_op" 0
| CT_proof_with(x1) ->
   fTACTIC_COM x1 ++
   fNODE "proof_with" 1
| CT_pwd -> fNODE "pwd" 0
| CT_quit -> fNODE "quit" 0
| CT_read_module(x1) ->
   fID x1 ++
   fNODE "read_module" 1
| CT_rec_ml_add_path(x1) ->
   fSTRING x1 ++
   fNODE "rec_ml_add_path" 1
| CT_recaddpath(x1, x2) ->
   fSTRING x1 ++
   fID_OPT x2 ++
   fNODE "recaddpath" 2
| CT_record(x1, x2, x3, x4, x5, x6) ->
   fCOERCION_OPT x1 ++
   fID x2 ++
   fBINDER_LIST x3 ++
   fFORMULA x4 ++
   fID_OPT x5 ++
   fRECCONSTR_LIST x6 ++
   fNODE "record" 6
| CT_remove_natural_feature(x1, x2) ->
   fNATURAL_FEATURE x1 ++
   fID x2 ++
   fNODE "remove_natural_feature" 2
| CT_require(x1, x2, x3) ->
   fIMPEXP x1 ++
   fSPEC_OPT x2 ++
   fID_NE_LIST_OR_STRING x3 ++
   fNODE "require" 3
| CT_reserve(x1, x2) ->
   fID_NE_LIST x1 ++
   fFORMULA x2 ++
   fNODE "reserve" 2
| CT_reserve_notation(x1, x2) ->
   fSTRING x1 ++
   fMODIFIER_LIST x2 ++
   fNODE "reserve_notation" 2
| CT_reset(x1) ->
   fID x1 ++
   fNODE "reset" 1
| CT_reset_section(x1) ->
   fID x1 ++
   fNODE "reset_section" 1
| CT_restart -> fNODE "restart" 0
| CT_restore_state(x1) ->
   fID x1 ++
   fNODE "restore_state" 1
| CT_resume(x1) ->
   fID_OPT x1 ++
   fNODE "resume" 1
| CT_save(x1, x2) ->
   fTHM_OPT x1 ++
   fID_OPT x2 ++
   fNODE "save" 2
| CT_scomments(x1) ->
   fSCOMMENT_CONTENT_LIST x1 ++
   fNODE "scomments" 1
| CT_search(x1, x2) ->
   fFORMULA x1 ++
   fIN_OR_OUT_MODULES x2 ++
   fNODE "search" 2
| CT_search_about(x1, x2) ->
   fID_OR_STRING_NE_LIST x1 ++
   fIN_OR_OUT_MODULES x2 ++
   fNODE "search_about" 2
| CT_search_pattern(x1, x2) ->
   fFORMULA x1 ++
   fIN_OR_OUT_MODULES x2 ++
   fNODE "search_pattern" 2
| CT_search_rewrite(x1, x2) ->
   fFORMULA x1 ++
   fIN_OR_OUT_MODULES x2 ++
   fNODE "search_rewrite" 2
| CT_section_end(x1) ->
   fID x1 ++
   fNODE "section_end" 1
| CT_section_struct(x1, x2, x3) ->
   fSECTION_BEGIN x1 ++
   fSECTION_BODY x2 ++
   fCOMMAND x3 ++
   fNODE "section_struct" 3
| CT_set_natural(x1) ->
   fID x1 ++
   fNODE "set_natural" 1
| CT_set_natural_default -> fNODE "set_natural_default" 0
| CT_set_option(x1) ->
   fTABLE x1 ++
   fNODE "set_option" 1
| CT_set_option_value(x1, x2) ->
   fTABLE x1 ++
   fSINGLE_OPTION_VALUE x2 ++
   fNODE "set_option_value" 2
| CT_set_option_value2(x1, x2) ->
   fTABLE x1 ++
   fID_OR_STRING_NE_LIST x2 ++
   fNODE "set_option_value2" 2
| CT_sethyp(x1) ->
   fINT x1 ++
   fNODE "sethyp" 1
| CT_setundo(x1) ->
   fINT x1 ++
   fNODE "setundo" 1
| CT_show_existentials -> fNODE "show_existentials" 0
| CT_show_goal(x1) ->
   fINT_OPT x1 ++
   fNODE "show_goal" 1
| CT_show_implicit(x1) ->
   fINT x1 ++
   fNODE "show_implicit" 1
| CT_show_intro -> fNODE "show_intro" 0
| CT_show_intros -> fNODE "show_intros" 0
| CT_show_node -> fNODE "show_node" 0
| CT_show_proof -> fNODE "show_proof" 0
| CT_show_proofs -> fNODE "show_proofs" 0
| CT_show_script -> fNODE "show_script" 0
| CT_show_tree -> fNODE "show_tree" 0
| CT_solve(x1, x2, x3) ->
   fINT x1 ++
   fTACTIC_COM x2 ++
   fDOTDOT_OPT x3 ++
   fNODE "solve" 3
| CT_strategy(CT_level_list x1) ->
   List.fold_left (++) (mt())
     (List.map (fun(l,q) -> fLEVEL l ++ fID_LIST q ++ fNODE "pair"2) x1) ++
   fNODE "strategy" (List.length x1)
| CT_suspend -> fNODE "suspend" 0
| CT_syntax_macro(x1, x2, x3) ->
   fID x1 ++
   fFORMULA x2 ++
   fINT_OPT x3 ++
   fNODE "syntax_macro" 3
| CT_tactic_definition(x1) ->
   fTAC_DEF_NE_LIST x1 ++
   fNODE "tactic_definition" 1
| CT_test_natural_feature(x1, x2) ->
   fNATURAL_FEATURE x1 ++
   fID x2 ++
   fNODE "test_natural_feature" 2
| CT_theorem_struct(x1, x2) ->
   fTHEOREM_GOAL x1 ++
   fPROOF_SCRIPT x2 ++
   fNODE "theorem_struct" 2
| CT_time(x1) ->
   fCOMMAND x1 ++
   fNODE "time" 1
| CT_undo(x1) ->
   fINT_OPT x1 ++
   fNODE "undo" 1
| CT_unfocus -> fNODE "unfocus" 0
| CT_unset_option(x1) ->
   fTABLE x1 ++
   fNODE "unset_option" 1
| CT_unsethyp -> fNODE "unsethyp" 0
| CT_unsetundo -> fNODE "unsetundo" 0
| CT_user_vernac(x1, x2) ->
   fID x1 ++
   fVARG_LIST x2 ++
   fNODE "user_vernac" 2
| CT_variable(x1, x2) ->
   fVAR x1 ++
   fBINDER_NE_LIST x2 ++
   fNODE "variable" 2
| CT_write_module(x1, x2) ->
   fID x1 ++
   fSTRING_OPT x2 ++
   fNODE "write_module" 2
and fLEVEL = function
| CT_Opaque -> fNODE "opaque" 0
| CT_Level n -> fINT n ++ fNODE "level" 1
| CT_Expand -> fNODE "expand" 0
and fCOMMAND_LIST = function
| CT_command_list(x,l) ->
   fCOMMAND x ++
   (List.fold_left (++) (mt()) (List.map fCOMMAND l)) ++
   fNODE "command_list" (1 + (List.length l))
and fCOMMENT = function
| CT_comment x -> fATOM "comment" ++
   (f_atom_string x) ++
   str "\n"
and fCOMMENT_S = function
| CT_comment_s l ->
   (List.fold_left (++) (mt()) (List.map fCOMMENT l)) ++
   fNODE "comment_s" (List.length l)
and fCONSTR = function
| CT_constr(x1, x2) ->
   fID x1 ++
   fFORMULA x2 ++
   fNODE "constr" 2
| CT_constr_coercion(x1, x2) ->
   fID x1 ++
   fFORMULA x2 ++
   fNODE "constr_coercion" 2
and fCONSTR_LIST = function
| CT_constr_list l ->
   (List.fold_left (++) (mt()) (List.map fCONSTR l)) ++
   fNODE "constr_list" (List.length l)
and fCONTEXT_HYP_LIST = function
| CT_context_hyp_list l ->
   (List.fold_left (++) (mt()) (List.map fPREMISE_PATTERN l)) ++
   fNODE "context_hyp_list" (List.length l)
and fCONTEXT_PATTERN = function
| CT_coerce_FORMULA_to_CONTEXT_PATTERN x -> fFORMULA x
| CT_context(x1, x2) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fNODE "context" 2
and fCONTEXT_RULE = function
| CT_context_rule(x1, x2, x3) ->
   fCONTEXT_HYP_LIST x1 ++
   fCONTEXT_PATTERN x2 ++
   fTACTIC_COM x3 ++
   fNODE "context_rule" 3
| CT_def_context_rule(x1) ->
   fTACTIC_COM x1 ++
   fNODE "def_context_rule" 1
and fCONVERSION_FLAG = function
| CT_beta -> fNODE "beta" 0
| CT_delta -> fNODE "delta" 0
| CT_evar -> fNODE "evar" 0
| CT_iota -> fNODE "iota" 0
| CT_zeta -> fNODE "zeta" 0
and fCONVERSION_FLAG_LIST = function
| CT_conversion_flag_list l ->
   (List.fold_left (++) (mt()) (List.map fCONVERSION_FLAG l)) ++
   fNODE "conversion_flag_list" (List.length l)
and fCONV_SET = function
| CT_unf l ->
   (List.fold_left (++) (mt()) (List.map fID l)) ++
   fNODE "unf" (List.length l)
| CT_unfbut l ->
   (List.fold_left (++) (mt()) (List.map fID l)) ++
   fNODE "unfbut" (List.length l)
and fCO_IND = function
| CT_co_ind x -> fATOM "co_ind" ++
   (f_atom_string x) ++
   str "\n"
and fDECL_NOTATION_OPT = function
| CT_coerce_NONE_to_DECL_NOTATION_OPT x -> fNONE x
| CT_decl_notation(x1, x2, x3) ->
   fSTRING x1 ++
   fFORMULA x2 ++
   fID_OPT x3 ++
   fNODE "decl_notation" 3
and fDEF = function
| CT_def(x1, x2) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fNODE "def" 2
and fDEFN = function
| CT_defn x -> fATOM "defn" ++
   (f_atom_string x) ++
   str "\n"
and fDEFN_OR_THM = function
| CT_coerce_DEFN_to_DEFN_OR_THM x -> fDEFN x
| CT_coerce_THM_to_DEFN_OR_THM x -> fTHM x
and fDEF_BODY = function
| CT_coerce_CONTEXT_PATTERN_to_DEF_BODY x -> fCONTEXT_PATTERN x
| CT_coerce_EVAL_CMD_to_DEF_BODY x -> fEVAL_CMD x
| CT_type_of(x1) ->
   fFORMULA x1 ++
   fNODE "type_of" 1
and fDEF_BODY_OPT = function
| CT_coerce_DEF_BODY_to_DEF_BODY_OPT x -> fDEF_BODY x
| CT_coerce_FORMULA_OPT_to_DEF_BODY_OPT x -> fFORMULA_OPT x
and fDEP = function
| CT_dep x -> fATOM "dep" ++
   (f_atom_string x) ++
   str "\n"
and fDESTRUCTING = function
| CT_coerce_NONE_to_DESTRUCTING x -> fNONE x
| CT_destructing -> fNODE "destructing" 0
and fDESTRUCT_LOCATION = function
| CT_conclusion_location -> fNODE "conclusion_location" 0
| CT_discardable_hypothesis -> fNODE "discardable_hypothesis" 0
| CT_hypothesis_location -> fNODE "hypothesis_location" 0
and fDOTDOT_OPT = function
| CT_coerce_NONE_to_DOTDOT_OPT x -> fNONE x
| CT_dotdot -> fNODE "dotdot" 0
and fEQN = function
| CT_eqn(x1, x2) ->
   fMATCH_PATTERN_NE_LIST x1 ++
   fFORMULA x2 ++
   fNODE "eqn" 2
and fEQN_LIST = function
| CT_eqn_list l ->
   (List.fold_left (++) (mt()) (List.map fEQN l)) ++
   fNODE "eqn_list" (List.length l)
and fEVAL_CMD = function
| CT_eval(x1, x2, x3) ->
   fINT_OPT x1 ++
   fRED_COM x2 ++
   fFORMULA x3 ++
   fNODE "eval" 3
and fFIXTAC = function
| CT_fixtac(x1, x2, x3) ->
   fID x1 ++
   fINT x2 ++
   fFORMULA x3 ++
   fNODE "fixtac" 3
and fFIX_BINDER = function
| CT_coerce_FIX_REC_to_FIX_BINDER x -> fFIX_REC x
| CT_fix_binder(x1, x2, x3, x4) ->
   fID x1 ++
   fINT x2 ++
   fFORMULA x3 ++
   fFORMULA x4 ++
   fNODE "fix_binder" 4
and fFIX_BINDER_LIST = function
| CT_fix_binder_list(x,l) ->
   fFIX_BINDER x ++
   (List.fold_left (++) (mt()) (List.map fFIX_BINDER l)) ++
   fNODE "fix_binder_list" (1 + (List.length l))
and fFIX_REC = function
| CT_fix_rec(x1, x2, x3, x4, x5) ->
   fID x1 ++
   fBINDER_NE_LIST x2 ++
   fID_OPT x3 ++
   fFORMULA x4 ++
   fFORMULA x5 ++
   fNODE "fix_rec" 5
and fFIX_REC_LIST = function
| CT_fix_rec_list(x,l) ->
   fFIX_REC x ++
   (List.fold_left (++) (mt()) (List.map fFIX_REC l)) ++
   fNODE "fix_rec_list" (1 + (List.length l))
and fFIX_TAC_LIST = function
| CT_fix_tac_list l ->
   (List.fold_left (++) (mt()) (List.map fFIXTAC l)) ++
   fNODE "fix_tac_list" (List.length l)
and fFORMULA = function
| CT_coerce_BINARY_to_FORMULA x -> fBINARY x
| CT_coerce_ID_to_FORMULA x -> fID x
| CT_coerce_NUM_to_FORMULA x -> fNUM x
| CT_coerce_SORT_TYPE_to_FORMULA x -> fSORT_TYPE x
| CT_coerce_TYPED_FORMULA_to_FORMULA x -> fTYPED_FORMULA x
| CT_appc(x1, x2) ->
   fFORMULA x1 ++
   fFORMULA_NE_LIST x2 ++
   fNODE "appc" 2
| CT_arrowc(x1, x2) ->
   fFORMULA x1 ++
   fFORMULA x2 ++
   fNODE "arrowc" 2
| CT_bang(x1) ->
   fFORMULA x1 ++
   fNODE "bang" 1
| CT_cases(x1, x2, x3) ->
   fMATCHED_FORMULA_NE_LIST x1 ++
   fFORMULA_OPT x2 ++
   fEQN_LIST x3 ++
   fNODE "cases" 3
| CT_cofixc(x1, x2) ->
   fID x1 ++
   fCOFIX_REC_LIST x2 ++
   fNODE "cofixc" 2
| CT_elimc(x1, x2, x3, x4) ->
   fCASE x1 ++
   fFORMULA_OPT x2 ++
   fFORMULA x3 ++
   fFORMULA_LIST x4 ++
   fNODE "elimc" 4
| CT_existvarc -> fNODE "existvarc" 0
| CT_fixc(x1, x2) ->
   fID x1 ++
   fFIX_BINDER_LIST x2 ++
   fNODE "fixc" 2
| CT_if(x1, x2, x3, x4) ->
   fFORMULA x1 ++
   fRETURN_INFO x2 ++
   fFORMULA x3 ++
   fFORMULA x4 ++
   fNODE "if" 4
| CT_inductive_let(x1, x2, x3, x4) ->
   fFORMULA_OPT x1 ++
   fID_OPT_NE_LIST x2 ++
   fFORMULA x3 ++
   fFORMULA x4 ++
   fNODE "inductive_let" 4
| CT_labelled_arg(x1, x2) ->
   fID x1 ++
   fFORMULA x2 ++
   fNODE "labelled_arg" 2
| CT_lambdac(x1, x2) ->
   fBINDER_NE_LIST x1 ++
   fFORMULA x2 ++
   fNODE "lambdac" 2
| CT_let_tuple(x1, x2, x3, x4) ->
   fID_OPT_NE_LIST x1 ++
   fRETURN_INFO x2 ++
   fFORMULA x3 ++
   fFORMULA x4 ++
   fNODE "let_tuple" 4
| CT_letin(x1, x2) ->
   fDEF x1 ++
   fFORMULA x2 ++
   fNODE "letin" 2
| CT_notation(x1, x2) ->
   fSTRING x1 ++
   fFORMULA_LIST x2 ++
   fNODE "notation" 2
| CT_num_encapsulator(x1, x2) ->
   fNUM_TYPE x1 ++
   fFORMULA x2 ++
   fNODE "num_encapsulator" 2
| CT_prodc(x1, x2) ->
   fBINDER_NE_LIST x1 ++
   fFORMULA x2 ++
   fNODE "prodc" 2
| CT_proj(x1, x2) ->
   fFORMULA x1 ++
   fFORMULA_NE_LIST x2 ++
   fNODE "proj" 2
and fFORMULA_LIST = function
| CT_formula_list l ->
   (List.fold_left (++) (mt()) (List.map fFORMULA l)) ++
   fNODE "formula_list" (List.length l)
and fFORMULA_NE_LIST = function
| CT_formula_ne_list(x,l) ->
   fFORMULA x ++
   (List.fold_left (++) (mt()) (List.map fFORMULA l)) ++
   fNODE "formula_ne_list" (1 + (List.length l))
and fFORMULA_OPT = function
| CT_coerce_FORMULA_to_FORMULA_OPT x -> fFORMULA x
| CT_coerce_ID_OPT_to_FORMULA_OPT x -> fID_OPT x
and fFORMULA_OR_INT = function
| CT_coerce_FORMULA_to_FORMULA_OR_INT x -> fFORMULA x
| CT_coerce_ID_OR_INT_to_FORMULA_OR_INT x -> fID_OR_INT x
and fGRAMMAR = function
| CT_grammar_none -> fNODE "grammar_none" 0
and fHYP_LOCATION = function
| CT_coerce_UNFOLD_to_HYP_LOCATION x -> fUNFOLD x
| CT_intype(x1, x2) ->
   fID x1 ++
   fINT_LIST x2 ++
   fNODE "intype" 2
| CT_invalue(x1, x2) ->
   fID x1 ++
   fINT_LIST x2 ++
   fNODE "invalue" 2
and fHYP_LOCATION_LIST_OR_STAR = function
| CT_coerce_STAR_to_HYP_LOCATION_LIST_OR_STAR x -> fSTAR x
| CT_hyp_location_list l ->
   (List.fold_left (++) (mt()) (List.map fHYP_LOCATION l)) ++
   fNODE "hyp_location_list" (List.length l)
and fID = function
| CT_ident x -> fATOM "ident" ++
   (f_atom_string x) ++
   str "\n"
| CT_metac(x1) ->
   fINT x1 ++
   fNODE "metac" 1
| CT_metaid x -> fATOM "metaid" ++
   (f_atom_string x) ++
   str "\n"
and fIDENTITY_OPT = function
| CT_coerce_NONE_to_IDENTITY_OPT x -> fNONE x
| CT_identity -> fNODE "identity" 0
and fID_LIST = function
| CT_id_list l ->
   (List.fold_left (++) (mt()) (List.map fID l)) ++
   fNODE "id_list" (List.length l)
and fID_LIST_LIST = function
| CT_id_list_list l ->
   (List.fold_left (++) (mt()) (List.map fID_LIST l)) ++
   fNODE "id_list_list" (List.length l)
and fID_LIST_OPT = function
| CT_coerce_ID_LIST_to_ID_LIST_OPT x -> fID_LIST x
| CT_coerce_NONE_to_ID_LIST_OPT x -> fNONE x
and fID_NE_LIST = function
| CT_id_ne_list(x,l) ->
   fID x ++
   (List.fold_left (++) (mt()) (List.map fID l)) ++
   fNODE "id_ne_list" (1 + (List.length l))
and fID_NE_LIST_OR_STAR = function
| CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR x -> fID_NE_LIST x
| CT_coerce_STAR_to_ID_NE_LIST_OR_STAR x -> fSTAR x
and fID_NE_LIST_OR_STRING = function
| CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STRING x -> fID_NE_LIST x
| CT_coerce_STRING_to_ID_NE_LIST_OR_STRING x -> fSTRING x
and fID_OPT = function
| CT_coerce_ID_to_ID_OPT x -> fID x
| CT_coerce_NONE_to_ID_OPT x -> fNONE x
and fID_OPT_LIST = function
| CT_id_opt_list l ->
   (List.fold_left (++) (mt()) (List.map fID_OPT l)) ++
   fNODE "id_opt_list" (List.length l)
and fID_OPT_NE_LIST = function
| CT_id_opt_ne_list(x,l) ->
   fID_OPT x ++
   (List.fold_left (++) (mt()) (List.map fID_OPT l)) ++
   fNODE "id_opt_ne_list" (1 + (List.length l))
and fID_OPT_OR_ALL = function
| CT_coerce_ID_OPT_to_ID_OPT_OR_ALL x -> fID_OPT x
| CT_all -> fNODE "all" 0
and fID_OR_INT = function
| CT_coerce_ID_to_ID_OR_INT x -> fID x
| CT_coerce_INT_to_ID_OR_INT x -> fINT x
and fID_OR_INT_OPT = function
| CT_coerce_ID_OPT_to_ID_OR_INT_OPT x -> fID_OPT x
| CT_coerce_ID_OR_INT_to_ID_OR_INT_OPT x -> fID_OR_INT x
| CT_coerce_INT_OPT_to_ID_OR_INT_OPT x -> fINT_OPT x
and fID_OR_STAR = function
| CT_coerce_ID_to_ID_OR_STAR x -> fID x
| CT_coerce_STAR_to_ID_OR_STAR x -> fSTAR x
and fID_OR_STRING = function
| CT_coerce_ID_to_ID_OR_STRING x -> fID x
| CT_coerce_STRING_to_ID_OR_STRING x -> fSTRING x
and fID_OR_STRING_NE_LIST = function
| CT_id_or_string_ne_list(x,l) ->
   fID_OR_STRING x ++
   (List.fold_left (++) (mt()) (List.map fID_OR_STRING l)) ++
   fNODE "id_or_string_ne_list" (1 + (List.length l))
and fIMPEXP = function
| CT_coerce_NONE_to_IMPEXP x -> fNONE x
| CT_export -> fNODE "export" 0
| CT_import -> fNODE "import" 0
and fIND_SPEC = function
| CT_ind_spec(x1, x2, x3, x4, x5) ->
   fID x1 ++
   fBINDER_LIST x2 ++
   fFORMULA x3 ++
   fCONSTR_LIST x4 ++
   fDECL_NOTATION_OPT x5 ++
   fNODE "ind_spec" 5
and fIND_SPEC_LIST = function
| CT_ind_spec_list l ->
   (List.fold_left (++) (mt()) (List.map fIND_SPEC l)) ++
   fNODE "ind_spec_list" (List.length l)
and fINT = function
| CT_int x -> fATOM "int" ++
   (f_atom_int x) ++
   str "\n"
and fINTRO_PATT = function
| CT_coerce_ID_to_INTRO_PATT x -> fID x
| CT_disj_pattern(x,l) ->
   fINTRO_PATT_LIST x ++
   (List.fold_left (++) (mt()) (List.map fINTRO_PATT_LIST l)) ++
   fNODE "disj_pattern" (1 + (List.length l))
and fINTRO_PATT_LIST = function
| CT_intro_patt_list l ->
   (List.fold_left (++) (mt()) (List.map fINTRO_PATT l)) ++
   fNODE "intro_patt_list" (List.length l)
and fINTRO_PATT_OPT = function
| CT_coerce_ID_OPT_to_INTRO_PATT_OPT x -> fID_OPT x
| CT_coerce_INTRO_PATT_to_INTRO_PATT_OPT x -> fINTRO_PATT x
and fINT_LIST = function
| CT_int_list l ->
   (List.fold_left (++) (mt()) (List.map fINT l)) ++
   fNODE "int_list" (List.length l)
and fINT_NE_LIST = function
| CT_int_ne_list(x,l) ->
   fINT x ++
   (List.fold_left (++) (mt()) (List.map fINT l)) ++
   fNODE "int_ne_list" (1 + (List.length l))
and fINT_OPT = function
| CT_coerce_INT_to_INT_OPT x -> fINT x
| CT_coerce_NONE_to_INT_OPT x -> fNONE x
and fINT_OR_LOCN = function
| CT_coerce_INT_to_INT_OR_LOCN x -> fINT x
| CT_coerce_LOCN_to_INT_OR_LOCN x -> fLOCN x
and fINT_OR_NEXT = function
| CT_coerce_INT_to_INT_OR_NEXT x -> fINT x
| CT_next_level -> fNODE "next_level" 0
and fINV_TYPE = function
| CT_inv_clear -> fNODE "inv_clear" 0
| CT_inv_regular -> fNODE "inv_regular" 0
| CT_inv_simple -> fNODE "inv_simple" 0
and fIN_OR_OUT_MODULES = function
| CT_coerce_NONE_to_IN_OR_OUT_MODULES x -> fNONE x
| CT_in_modules(x1) ->
   fID_NE_LIST x1 ++
   fNODE "in_modules" 1
| CT_out_modules(x1) ->
   fID_NE_LIST x1 ++
   fNODE "out_modules" 1
and fLET_CLAUSE = function
| CT_let_clause(x1, x2, x3) ->
   fID x1 ++
   fTACTIC_OPT x2 ++
   fLET_VALUE x3 ++
   fNODE "let_clause" 3
and fLET_CLAUSES = function
| CT_let_clauses(x,l) ->
   fLET_CLAUSE x ++
   (List.fold_left (++) (mt()) (List.map fLET_CLAUSE l)) ++
   fNODE "let_clauses" (1 + (List.length l))
and fLET_VALUE = function
| CT_coerce_DEF_BODY_to_LET_VALUE x -> fDEF_BODY x
| CT_coerce_TACTIC_COM_to_LET_VALUE x -> fTACTIC_COM x
and fLOCAL_OPT = function
| CT_coerce_NONE_to_LOCAL_OPT x -> fNONE x
| CT_local -> fNODE "local" 0
and fLOCN = function
| CT_locn x -> fATOM "locn" ++
   (f_atom_string x) ++
   str "\n"
and fMATCHED_FORMULA = function
| CT_coerce_FORMULA_to_MATCHED_FORMULA x -> fFORMULA x
| CT_formula_as(x1, x2) ->
   fFORMULA x1 ++
   fID_OPT x2 ++
   fNODE "formula_as" 2
| CT_formula_as_in(x1, x2, x3) ->
   fFORMULA x1 ++
   fID_OPT x2 ++
   fFORMULA x3 ++
   fNODE "formula_as_in" 3
| CT_formula_in(x1, x2) ->
   fFORMULA x1 ++
   fFORMULA x2 ++
   fNODE "formula_in" 2
and fMATCHED_FORMULA_NE_LIST = function
| CT_matched_formula_ne_list(x,l) ->
   fMATCHED_FORMULA x ++
   (List.fold_left (++) (mt()) (List.map fMATCHED_FORMULA l)) ++
   fNODE "matched_formula_ne_list" (1 + (List.length l))
and fMATCH_PATTERN = function
| CT_coerce_ID_OPT_to_MATCH_PATTERN x -> fID_OPT x
| CT_coerce_NUM_to_MATCH_PATTERN x -> fNUM x
| CT_pattern_app(x1, x2) ->
   fMATCH_PATTERN x1 ++
   fMATCH_PATTERN_NE_LIST x2 ++
   fNODE "pattern_app" 2
| CT_pattern_as(x1, x2) ->
   fMATCH_PATTERN x1 ++
   fID_OPT x2 ++
   fNODE "pattern_as" 2
| CT_pattern_delimitors(x1, x2) ->
   fNUM_TYPE x1 ++
   fMATCH_PATTERN x2 ++
   fNODE "pattern_delimitors" 2
| CT_pattern_notation(x1, x2) ->
   fSTRING x1 ++
   fMATCH_PATTERN_LIST x2 ++
   fNODE "pattern_notation" 2
and fMATCH_PATTERN_LIST = function
| CT_match_pattern_list l ->
   (List.fold_left (++) (mt()) (List.map fMATCH_PATTERN l)) ++
   fNODE "match_pattern_list" (List.length l)
and fMATCH_PATTERN_NE_LIST = function
| CT_match_pattern_ne_list(x,l) ->
   fMATCH_PATTERN x ++
   (List.fold_left (++) (mt()) (List.map fMATCH_PATTERN l)) ++
   fNODE "match_pattern_ne_list" (1 + (List.length l))
and fMATCH_TAC_RULE = function
| CT_match_tac_rule(x1, x2) ->
   fCONTEXT_PATTERN x1 ++
   fLET_VALUE x2 ++
   fNODE "match_tac_rule" 2
and fMATCH_TAC_RULES = function
| CT_match_tac_rules(x,l) ->
   fMATCH_TAC_RULE x ++
   (List.fold_left (++) (mt()) (List.map fMATCH_TAC_RULE l)) ++
   fNODE "match_tac_rules" (1 + (List.length l))
and fMODIFIER = function
| CT_entry_type(x1, x2) ->
   fID x1 ++
   fID x2 ++
   fNODE "entry_type" 2
| CT_format(x1) ->
   fSTRING x1 ++
   fNODE "format" 1
| CT_lefta -> fNODE "lefta" 0
| CT_nona -> fNODE "nona" 0
| CT_only_parsing -> fNODE "only_parsing" 0
| CT_righta -> fNODE "righta" 0
| CT_set_item_level(x1, x2) ->
   fID_NE_LIST x1 ++
   fINT_OR_NEXT x2 ++
   fNODE "set_item_level" 2
| CT_set_level(x1) ->
   fINT x1 ++
   fNODE "set_level" 1
and fMODIFIER_LIST = function
| CT_modifier_list l ->
   (List.fold_left (++) (mt()) (List.map fMODIFIER l)) ++
   fNODE "modifier_list" (List.length l)
and fMODULE_BINDER = function
| CT_module_binder(x1, x2) ->
   fID_NE_LIST x1 ++
   fMODULE_TYPE x2 ++
   fNODE "module_binder" 2
and fMODULE_BINDER_LIST = function
| CT_module_binder_list l ->
   (List.fold_left (++) (mt()) (List.map fMODULE_BINDER l)) ++
   fNODE "module_binder_list" (List.length l)
and fMODULE_EXPR = function
| CT_coerce_ID_OPT_to_MODULE_EXPR x -> fID_OPT x
| CT_module_app(x1, x2) ->
   fMODULE_EXPR x1 ++
   fMODULE_EXPR x2 ++
   fNODE "module_app" 2
and fMODULE_TYPE = function
| CT_coerce_ID_to_MODULE_TYPE x -> fID x
| CT_module_type_with_def(x1, x2, x3) ->
   fMODULE_TYPE x1 ++
   fID_LIST x2 ++
   fFORMULA x3 ++
   fNODE "module_type_with_def" 3
| CT_module_type_with_mod(x1, x2, x3) ->
   fMODULE_TYPE x1 ++
   fID_LIST x2 ++
   fID x3 ++
   fNODE "module_type_with_mod" 3
and fMODULE_TYPE_CHECK = function
| CT_coerce_MODULE_TYPE_OPT_to_MODULE_TYPE_CHECK x -> fMODULE_TYPE_OPT x
| CT_only_check(x1) ->
   fMODULE_TYPE x1 ++
   fNODE "only_check" 1
and fMODULE_TYPE_OPT = function
| CT_coerce_ID_OPT_to_MODULE_TYPE_OPT x -> fID_OPT x
| CT_coerce_MODULE_TYPE_to_MODULE_TYPE_OPT x -> fMODULE_TYPE x
and fNATURAL_FEATURE = function
| CT_contractible -> fNODE "contractible" 0
| CT_implicit -> fNODE "implicit" 0
| CT_nat_transparent -> fNODE "nat_transparent" 0
and fNONE = function
| CT_none -> fNODE "none" 0
and fNUM = function
| CT_int_encapsulator x -> fATOM "int_encapsulator" ++
   (f_atom_string x) ++
   str "\n"
and fNUM_TYPE = function
| CT_num_type x -> fATOM "num_type" ++
   (f_atom_string x) ++
   str "\n"
and fOMEGA_FEATURE = function
| CT_coerce_STRING_to_OMEGA_FEATURE x -> fSTRING x
| CT_flag_action -> fNODE "flag_action" 0
| CT_flag_system -> fNODE "flag_system" 0
| CT_flag_time -> fNODE "flag_time" 0
and fOMEGA_MODE = function
| CT_set -> fNODE "set" 0
| CT_switch -> fNODE "switch" 0
| CT_unset -> fNODE "unset" 0
and fORIENTATION = function
| CT_lr -> fNODE "lr" 0
| CT_rl -> fNODE "rl" 0
and fPATTERN = function
| CT_pattern_occ(x1, x2) ->
   fINT_LIST x1 ++
   fFORMULA x2 ++
   fNODE "pattern_occ" 2
and fPATTERN_NE_LIST = function
| CT_pattern_ne_list(x,l) ->
   fPATTERN x ++
   (List.fold_left (++) (mt()) (List.map fPATTERN l)) ++
   fNODE "pattern_ne_list" (1 + (List.length l))
and fPATTERN_OPT = function
| CT_coerce_NONE_to_PATTERN_OPT x -> fNONE x
| CT_coerce_PATTERN_to_PATTERN_OPT x -> fPATTERN x
and fPREMISE = function
| CT_coerce_TYPED_FORMULA_to_PREMISE x -> fTYPED_FORMULA x
| CT_eval_result(x1, x2, x3) ->
   fFORMULA x1 ++
   fFORMULA x2 ++
   fFORMULA x3 ++
   fNODE "eval_result" 3
| CT_premise(x1, x2) ->
   fID x1 ++
   fFORMULA x2 ++
   fNODE "premise" 2
and fPREMISES_LIST = function
| CT_premises_list l ->
   (List.fold_left (++) (mt()) (List.map fPREMISE l)) ++
   fNODE "premises_list" (List.length l)
and fPREMISE_PATTERN = function
| CT_premise_pattern(x1, x2) ->
   fID_OPT x1 ++
   fCONTEXT_PATTERN x2 ++
   fNODE "premise_pattern" 2
and fPROOF_SCRIPT = function
| CT_proof_script l ->
   (List.fold_left (++) (mt()) (List.map fCOMMAND l)) ++
   fNODE "proof_script" (List.length l)
and fRECCONSTR = function
| CT_defrecconstr(x1, x2, x3) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fFORMULA_OPT x3 ++
   fNODE "defrecconstr" 3
| CT_defrecconstr_coercion(x1, x2, x3) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fFORMULA_OPT x3 ++
   fNODE "defrecconstr_coercion" 3
| CT_recconstr(x1, x2) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fNODE "recconstr" 2
| CT_recconstr_coercion(x1, x2) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fNODE "recconstr_coercion" 2
and fRECCONSTR_LIST = function
| CT_recconstr_list l ->
   (List.fold_left (++) (mt()) (List.map fRECCONSTR l)) ++
   fNODE "recconstr_list" (List.length l)
and fREC_TACTIC_FUN = function
| CT_rec_tactic_fun(x1, x2, x3) ->
   fID x1 ++
   fID_OPT_NE_LIST x2 ++
   fTACTIC_COM x3 ++
   fNODE "rec_tactic_fun" 3
and fREC_TACTIC_FUN_LIST = function
| CT_rec_tactic_fun_list(x,l) ->
   fREC_TACTIC_FUN x ++
   (List.fold_left (++) (mt()) (List.map fREC_TACTIC_FUN l)) ++
   fNODE "rec_tactic_fun_list" (1 + (List.length l))
and fRED_COM = function
| CT_cbv(x1, x2) ->
   fCONVERSION_FLAG_LIST x1 ++
   fCONV_SET x2 ++
   fNODE "cbv" 2
| CT_fold(x1) ->
   fFORMULA_LIST x1 ++
   fNODE "fold" 1
| CT_hnf -> fNODE "hnf" 0
| CT_lazy(x1, x2) ->
   fCONVERSION_FLAG_LIST x1 ++
   fCONV_SET x2 ++
   fNODE "lazy" 2
| CT_pattern(x1) ->
   fPATTERN_NE_LIST x1 ++
   fNODE "pattern" 1
| CT_red -> fNODE "red" 0
| CT_cbvvm -> fNODE "vm_compute" 0
| CT_simpl(x1) ->
   fPATTERN_OPT x1 ++
   fNODE "simpl" 1
| CT_unfold(x1) ->
   fUNFOLD_NE_LIST x1 ++
   fNODE "unfold" 1
and fRETURN_INFO = function
| CT_coerce_NONE_to_RETURN_INFO x -> fNONE x
| CT_as_and_return(x1, x2) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fNODE "as_and_return" 2
| CT_return(x1) ->
   fFORMULA x1 ++
   fNODE "return" 1
and fRULE = function
| CT_rule(x1, x2) ->
   fPREMISES_LIST x1 ++
   fFORMULA x2 ++
   fNODE "rule" 2
and fRULE_LIST = function
| CT_rule_list l ->
   (List.fold_left (++) (mt()) (List.map fRULE l)) ++
   fNODE "rule_list" (List.length l)
and fSCHEME_SPEC = function
| CT_scheme_spec(x1, x2, x3, x4) ->
   fID x1 ++
   fDEP x2 ++
   fFORMULA x3 ++
   fSORT_TYPE x4 ++
   fNODE "scheme_spec" 4
and fSCHEME_SPEC_LIST = function
| CT_scheme_spec_list(x,l) ->
   fSCHEME_SPEC x ++
   (List.fold_left (++) (mt()) (List.map fSCHEME_SPEC l)) ++
   fNODE "scheme_spec_list" (1 + (List.length l))
and fSCOMMENT_CONTENT = function
| CT_coerce_FORMULA_to_SCOMMENT_CONTENT x -> fFORMULA x
| CT_coerce_ID_OR_STRING_to_SCOMMENT_CONTENT x -> fID_OR_STRING x
and fSCOMMENT_CONTENT_LIST = function
| CT_scomment_content_list l ->
   (List.fold_left (++) (mt()) (List.map fSCOMMENT_CONTENT l)) ++
   fNODE "scomment_content_list" (List.length l)
and fSECTION_BEGIN = function
| CT_section(x1) ->
   fID x1 ++
   fNODE "section" 1
and fSECTION_BODY = function
| CT_section_body l ->
   (List.fold_left (++) (mt()) (List.map fCOMMAND l)) ++
   fNODE "section_body" (List.length l)
and fSIGNED_INT = function
| CT_coerce_INT_to_SIGNED_INT x -> fINT x
| CT_minus(x1) ->
   fINT x1 ++
   fNODE "minus" 1
and fSIGNED_INT_LIST = function
| CT_signed_int_list l ->
   (List.fold_left (++) (mt()) (List.map fSIGNED_INT l)) ++
   fNODE "signed_int_list" (List.length l)
and fSINGLE_OPTION_VALUE = function
| CT_coerce_INT_to_SINGLE_OPTION_VALUE x -> fINT x
| CT_coerce_STRING_to_SINGLE_OPTION_VALUE x -> fSTRING x
and fSORT_TYPE = function
| CT_sortc x -> fATOM "sortc" ++
   (f_atom_string x) ++
   str "\n"
and fSPEC_LIST = function
| CT_coerce_BINDING_LIST_to_SPEC_LIST x -> fBINDING_LIST x
| CT_coerce_FORMULA_LIST_to_SPEC_LIST x -> fFORMULA_LIST x
and fSPEC_OPT = function
| CT_coerce_NONE_to_SPEC_OPT x -> fNONE x
| CT_spec -> fNODE "spec" 0
and fSTAR = function
| CT_star -> fNODE "star" 0
and fSTAR_OPT = function
| CT_coerce_NONE_to_STAR_OPT x -> fNONE x
| CT_coerce_STAR_to_STAR_OPT x -> fSTAR x
and fSTRING = function
| CT_string x -> fATOM "string" ++
   (f_atom_string x) ++
   str "\n"
and fSTRING_NE_LIST = function
| CT_string_ne_list(x,l) ->
   fSTRING x ++
   (List.fold_left (++) (mt()) (List.map fSTRING l)) ++
   fNODE "string_ne_list" (1 + (List.length l))
and fSTRING_OPT = function
| CT_coerce_NONE_to_STRING_OPT x -> fNONE x
| CT_coerce_STRING_to_STRING_OPT x -> fSTRING x
and fTABLE = function
| CT_coerce_ID_to_TABLE x -> fID x
| CT_table(x1, x2) ->
   fID x1 ++
   fID x2 ++
   fNODE "table" 2
and fTACTIC_ARG = function
| CT_coerce_EVAL_CMD_to_TACTIC_ARG x -> fEVAL_CMD x
| CT_coerce_FORMULA_OR_INT_to_TACTIC_ARG x -> fFORMULA_OR_INT x
| CT_coerce_TACTIC_COM_to_TACTIC_ARG x -> fTACTIC_COM x
| CT_coerce_TERM_CHANGE_to_TACTIC_ARG x -> fTERM_CHANGE x
| CT_void -> fNODE "void" 0
and fTACTIC_ARG_LIST = function
| CT_tactic_arg_list(x,l) ->
   fTACTIC_ARG x ++
   (List.fold_left (++) (mt()) (List.map fTACTIC_ARG l)) ++
   fNODE "tactic_arg_list" (1 + (List.length l))
and fTACTIC_COM = function
| CT_abstract(x1, x2) ->
   fID_OPT x1 ++
   fTACTIC_COM x2 ++
   fNODE "abstract" 2
| CT_absurd(x1) ->
   fFORMULA x1 ++
   fNODE "absurd" 1
| CT_any_constructor(x1) ->
   fTACTIC_OPT x1 ++
   fNODE "any_constructor" 1
| CT_apply(x1, x2) ->
   fFORMULA x1 ++
   fSPEC_LIST x2 ++
   fNODE "apply" 2
| CT_assert(x1, x2) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fNODE "assert" 2
| CT_assumption -> fNODE "assumption" 0
| CT_auto(x1) ->
   fINT_OPT x1 ++
   fNODE "auto" 1
| CT_auto_with(x1, x2) ->
   fINT_OPT x1 ++
   fID_NE_LIST_OR_STAR x2 ++
   fNODE "auto_with" 2
| CT_autorewrite(x1, x2) ->
   fID_NE_LIST x1 ++
   fTACTIC_OPT x2 ++
   fNODE "autorewrite" 2
| CT_autotdb(x1) ->
   fINT_OPT x1 ++
   fNODE "autotdb" 1
| CT_case_type(x1) ->
   fFORMULA x1 ++
   fNODE "case_type" 1
| CT_casetac(x1, x2) ->
   fFORMULA x1 ++
   fSPEC_LIST x2 ++
   fNODE "casetac" 2
| CT_cdhyp(x1) ->
   fID x1 ++
   fNODE "cdhyp" 1
| CT_change(x1, x2) ->
   fFORMULA x1 ++
   fCLAUSE x2 ++
   fNODE "change" 2
| CT_change_local(x1, x2, x3) ->
   fPATTERN x1 ++
   fFORMULA x2 ++
   fCLAUSE x3 ++
   fNODE "change_local" 3
| CT_clear(x1) ->
   fID_NE_LIST x1 ++
   fNODE "clear" 1
| CT_clear_body(x1) ->
   fID_NE_LIST x1 ++
   fNODE "clear_body" 1
| CT_cofixtactic(x1, x2) ->
   fID_OPT x1 ++
   fCOFIX_TAC_LIST x2 ++
   fNODE "cofixtactic" 2
| CT_condrewrite_lr(x1, x2, x3, x4) ->
   fTACTIC_COM x1 ++
   fFORMULA x2 ++
   fSPEC_LIST x3 ++
   fID_OPT x4 ++
   fNODE "condrewrite_lr" 4
| CT_condrewrite_rl(x1, x2, x3, x4) ->
   fTACTIC_COM x1 ++
   fFORMULA x2 ++
   fSPEC_LIST x3 ++
   fID_OPT x4 ++
   fNODE "condrewrite_rl" 4
| CT_constructor(x1, x2) ->
   fINT x1 ++
   fSPEC_LIST x2 ++
   fNODE "constructor" 2
| CT_contradiction -> fNODE "contradiction" 0
| CT_contradiction_thm(x1, x2) ->
   fFORMULA x1 ++
   fSPEC_LIST x2 ++
   fNODE "contradiction_thm" 2
| CT_cut(x1) ->
   fFORMULA x1 ++
   fNODE "cut" 1
| CT_cutrewrite_lr(x1, x2) ->
   fFORMULA x1 ++
   fID_OPT x2 ++
   fNODE "cutrewrite_lr" 2
| CT_cutrewrite_rl(x1, x2) ->
   fFORMULA x1 ++
   fID_OPT x2 ++
   fNODE "cutrewrite_rl" 2
| CT_dauto(x1, x2) ->
   fINT_OPT x1 ++
   fINT_OPT x2 ++
   fNODE "dauto" 2
| CT_dconcl -> fNODE "dconcl" 0
| CT_decompose_list(x1, x2) ->
   fID_NE_LIST x1 ++
   fFORMULA x2 ++
   fNODE "decompose_list" 2
| CT_decompose_record(x1) ->
   fFORMULA x1 ++
   fNODE "decompose_record" 1
| CT_decompose_sum(x1) ->
   fFORMULA x1 ++
   fNODE "decompose_sum" 1
| CT_depinversion(x1, x2, x3, x4) ->
   fINV_TYPE x1 ++
   fID_OR_INT x2 ++
   fINTRO_PATT_OPT x3 ++
   fFORMULA_OPT x4 ++
   fNODE "depinversion" 4
| CT_deprewrite_lr(x1) ->
   fID x1 ++
   fNODE "deprewrite_lr" 1
| CT_deprewrite_rl(x1) ->
   fID x1 ++
   fNODE "deprewrite_rl" 1
| CT_destruct(x1) ->
   fID_OR_INT x1 ++
   fNODE "destruct" 1
| CT_dhyp(x1) ->
   fID x1 ++
   fNODE "dhyp" 1
| CT_discriminate_eq(x1) ->
   fID_OR_INT_OPT x1 ++
   fNODE "discriminate_eq" 1
| CT_do(x1, x2) ->
   fID_OR_INT x1 ++
   fTACTIC_COM x2 ++
   fNODE "do" 2
| CT_eapply(x1, x2) ->
   fFORMULA x1 ++
   fSPEC_LIST x2 ++
   fNODE "eapply" 2
| CT_eauto(x1, x2) ->
   fID_OR_INT_OPT x1 ++
   fID_OR_INT_OPT x2 ++
   fNODE "eauto" 2
| CT_eauto_with(x1, x2, x3) ->
   fID_OR_INT_OPT x1 ++
   fID_OR_INT_OPT x2 ++
   fID_NE_LIST_OR_STAR x3 ++
   fNODE "eauto_with" 3
| CT_elim(x1, x2, x3) ->
   fFORMULA x1 ++
   fSPEC_LIST x2 ++
   fUSING x3 ++
   fNODE "elim" 3
| CT_elim_type(x1) ->
   fFORMULA x1 ++
   fNODE "elim_type" 1
| CT_exact(x1) ->
   fFORMULA x1 ++
   fNODE "exact" 1
| CT_exact_no_check(x1) ->
   fFORMULA x1 ++
   fNODE "exact_no_check" 1
| CT_vm_cast_no_check(x1) ->
   fFORMULA x1 ++
   fNODE "vm_cast_no_check" 1
| CT_exists(x1) ->
   fSPEC_LIST x1 ++
   fNODE "exists" 1
| CT_fail(x1, x2) ->
   fID_OR_INT x1 ++
   fSTRING_OPT x2 ++
   fNODE "fail" 2
| CT_first(x,l) ->
   fTACTIC_COM x ++
   (List.fold_left (++) (mt()) (List.map fTACTIC_COM l)) ++
   fNODE "first" (1 + (List.length l))
| CT_firstorder(x1) ->
   fTACTIC_OPT x1 ++
   fNODE "firstorder" 1
| CT_firstorder_using(x1, x2) ->
   fTACTIC_OPT x1 ++
   fID_NE_LIST x2 ++
   fNODE "firstorder_using" 2
| CT_firstorder_with(x1, x2) ->
   fTACTIC_OPT x1 ++
   fID_NE_LIST x2 ++
   fNODE "firstorder_with" 2
| CT_fixtactic(x1, x2, x3) ->
   fID_OPT x1 ++
   fINT x2 ++
   fFIX_TAC_LIST x3 ++
   fNODE "fixtactic" 3
| CT_formula_marker(x1) ->
   fFORMULA x1 ++
   fNODE "formula_marker" 1
| CT_fresh(x1) ->
   fSTRING_OPT x1 ++
   fNODE "fresh" 1
| CT_generalize(x1) ->
   fFORMULA_NE_LIST x1 ++
   fNODE "generalize" 1
| CT_generalize_dependent(x1) ->
   fFORMULA x1 ++
   fNODE "generalize_dependent" 1
| CT_idtac(x1) ->
   fSTRING_OPT x1 ++
   fNODE "idtac" 1
| CT_induction(x1) ->
   fID_OR_INT x1 ++
   fNODE "induction" 1
| CT_info(x1) ->
   fTACTIC_COM x1 ++
   fNODE "info" 1
| CT_injection_eq(x1) ->
   fID_OR_INT_OPT x1 ++
   fNODE "injection_eq" 1
| CT_instantiate(x1, x2, x3) ->
   fINT x1 ++
   fFORMULA x2 ++
   fCLAUSE x3 ++
   fNODE "instantiate" 3
| CT_intro(x1) ->
   fID_OPT x1 ++
   fNODE "intro" 1
| CT_intro_after(x1, x2) ->
   fID_OPT x1 ++
   fID x2 ++
   fNODE "intro_after" 2
| CT_intros(x1) ->
   fINTRO_PATT_LIST x1 ++
   fNODE "intros" 1
| CT_intros_until(x1) ->
   fID_OR_INT x1 ++
   fNODE "intros_until" 1
| CT_inversion(x1, x2, x3, x4) ->
   fINV_TYPE x1 ++
   fID_OR_INT x2 ++
   fINTRO_PATT_OPT x3 ++
   fID_LIST x4 ++
   fNODE "inversion" 4
| CT_left(x1) ->
   fSPEC_LIST x1 ++
   fNODE "left" 1
| CT_let_ltac(x1, x2) ->
   fLET_CLAUSES x1 ++
   fLET_VALUE x2 ++
   fNODE "let_ltac" 2
| CT_lettac(x1, x2, x3) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fCLAUSE x3 ++
   fNODE "lettac" 3
| CT_match_context(x,l) ->
   fCONTEXT_RULE x ++
   (List.fold_left (++) (mt()) (List.map fCONTEXT_RULE l)) ++
   fNODE "match_context" (1 + (List.length l))
| CT_match_context_reverse(x,l) ->
   fCONTEXT_RULE x ++
   (List.fold_left (++) (mt()) (List.map fCONTEXT_RULE l)) ++
   fNODE "match_context_reverse" (1 + (List.length l))
| CT_match_tac(x1, x2) ->
   fTACTIC_COM x1 ++
   fMATCH_TAC_RULES x2 ++
   fNODE "match_tac" 2
| CT_move_after(x1, x2) ->
   fID x1 ++
   fID x2 ++
   fNODE "move_after" 2
| CT_new_destruct(x1, x2, x3) ->
   (List.fold_left (++) (mt()) (List.map fFORMULA_OR_INT x1)) ++ (* Julien F. Est-ce correct? *)
   fUSING x2 ++
   fINTRO_PATT_OPT x3 ++
   fNODE "new_destruct" 3
| CT_new_induction(x1, x2, x3) ->
   (List.fold_left (++) (mt()) (List.map fFORMULA_OR_INT x1)) ++ (* Pierre C. Est-ce correct? *)
   fUSING x2 ++
   fINTRO_PATT_OPT x3 ++
   fNODE "new_induction" 3
| CT_omega -> fNODE "omega" 0
| CT_orelse(x1, x2) ->
   fTACTIC_COM x1 ++
   fTACTIC_COM x2 ++
   fNODE "orelse" 2
| CT_parallel(x,l) ->
   fTACTIC_COM x ++
   (List.fold_left (++) (mt()) (List.map fTACTIC_COM l)) ++
   fNODE "parallel" (1 + (List.length l))
| CT_pose(x1, x2) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fNODE "pose" 2
| CT_progress(x1) ->
   fTACTIC_COM x1 ++
   fNODE "progress" 1
| CT_prolog(x1, x2) ->
   fFORMULA_LIST x1 ++
   fINT x2 ++
   fNODE "prolog" 2
| CT_rec_tactic_in(x1, x2) ->
   fREC_TACTIC_FUN_LIST x1 ++
   fTACTIC_COM x2 ++
   fNODE "rec_tactic_in" 2
| CT_reduce(x1, x2) ->
   fRED_COM x1 ++
   fCLAUSE x2 ++
   fNODE "reduce" 2
| CT_refine(x1) ->
   fFORMULA x1 ++
   fNODE "refine" 1
| CT_reflexivity -> fNODE "reflexivity" 0
| CT_rename(x1, x2) ->
   fID x1 ++
   fID x2 ++
   fNODE "rename" 2
| CT_repeat(x1) ->
   fTACTIC_COM x1 ++
   fNODE "repeat" 1
| CT_replace_with(x1, x2,x3,x4) ->
   fFORMULA x1 ++
   fFORMULA x2 ++
   fCLAUSE x3 ++
   fTACTIC_OPT x4 ++
   fNODE "replace_with" 4
| CT_rewrite_lr(x1, x2, x3) ->
   fFORMULA x1 ++
   fSPEC_LIST x2 ++
   fCLAUSE x3 ++
   fNODE "rewrite_lr" 3
| CT_rewrite_rl(x1, x2, x3) ->
   fFORMULA x1 ++
   fSPEC_LIST x2 ++
   fCLAUSE x3 ++
   fNODE "rewrite_rl" 3
| CT_right(x1) ->
   fSPEC_LIST x1 ++
   fNODE "right" 1
| CT_ring(x1) ->
   fFORMULA_LIST x1 ++
   fNODE "ring" 1
| CT_simple_user_tac(x1, x2) ->
   fID x1 ++
   fTACTIC_ARG_LIST x2 ++
   fNODE "simple_user_tac" 2
| CT_simplify_eq(x1) ->
   fID_OR_INT_OPT x1 ++
   fNODE "simplify_eq" 1
| CT_specialize(x1, x2, x3) ->
   fINT_OPT x1 ++
   fFORMULA x2 ++
   fSPEC_LIST x3 ++
   fNODE "specialize" 3
| CT_split(x1) ->
   fSPEC_LIST x1 ++
   fNODE "split" 1
| CT_subst(x1) ->
   fID_LIST x1 ++
   fNODE "subst" 1
| CT_superauto(x1, x2, x3, x4) ->
   fINT_OPT x1 ++
   fID_LIST x2 ++
   fDESTRUCTING x3 ++
   fUSINGTDB x4 ++
   fNODE "superauto" 4
| CT_symmetry(x1) ->
   fCLAUSE x1 ++
   fNODE "symmetry" 1
| CT_tac_double(x1, x2) ->
   fID_OR_INT x1 ++
   fID_OR_INT x2 ++
   fNODE "tac_double" 2
| CT_tacsolve(x,l) ->
   fTACTIC_COM x ++
   (List.fold_left (++) (mt()) (List.map fTACTIC_COM l)) ++
   fNODE "tacsolve" (1 + (List.length l))
| CT_tactic_fun(x1, x2) ->
   fID_OPT_NE_LIST x1 ++
   fTACTIC_COM x2 ++
   fNODE "tactic_fun" 2
| CT_then(x,l) ->
   fTACTIC_COM x ++
   (List.fold_left (++) (mt()) (List.map fTACTIC_COM l)) ++
   fNODE "then" (1 + (List.length l))
| CT_transitivity(x1) ->
   fFORMULA x1 ++
   fNODE "transitivity" 1
| CT_trivial -> fNODE "trivial" 0
| CT_trivial_with(x1) ->
   fID_NE_LIST_OR_STAR x1 ++
   fNODE "trivial_with" 1
| CT_truecut(x1, x2) ->
   fID_OPT x1 ++
   fFORMULA x2 ++
   fNODE "truecut" 2
| CT_try(x1) ->
   fTACTIC_COM x1 ++
   fNODE "try" 1
| CT_use(x1) ->
   fFORMULA x1 ++
   fNODE "use" 1
| CT_use_inversion(x1, x2, x3) ->
   fID_OR_INT x1 ++
   fFORMULA x2 ++
   fID_LIST x3 ++
   fNODE "use_inversion" 3
| CT_user_tac(x1, x2) ->
   fID x1 ++
   fTARG_LIST x2 ++
   fNODE "user_tac" 2
and fTACTIC_OPT = function
| CT_coerce_NONE_to_TACTIC_OPT x -> fNONE x
| CT_coerce_TACTIC_COM_to_TACTIC_OPT x -> fTACTIC_COM x
and fTAC_DEF = function
| CT_tac_def(x1, x2) ->
   fID x1 ++
   fTACTIC_COM x2 ++
   fNODE "tac_def" 2
and fTAC_DEF_NE_LIST = function
| CT_tac_def_ne_list(x,l) ->
   fTAC_DEF x ++
   (List.fold_left (++) (mt()) (List.map fTAC_DEF l)) ++
   fNODE "tac_def_ne_list" (1 + (List.length l))
and fTARG = function
| CT_coerce_BINDING_to_TARG x -> fBINDING x
| CT_coerce_COFIXTAC_to_TARG x -> fCOFIXTAC x
| CT_coerce_FIXTAC_to_TARG x -> fFIXTAC x
| CT_coerce_FORMULA_OR_INT_to_TARG x -> fFORMULA_OR_INT x
| CT_coerce_PATTERN_to_TARG x -> fPATTERN x
| CT_coerce_SCOMMENT_CONTENT_to_TARG x -> fSCOMMENT_CONTENT x
| CT_coerce_SIGNED_INT_LIST_to_TARG x -> fSIGNED_INT_LIST x
| CT_coerce_SINGLE_OPTION_VALUE_to_TARG x -> fSINGLE_OPTION_VALUE x
| CT_coerce_SPEC_LIST_to_TARG x -> fSPEC_LIST x
| CT_coerce_TACTIC_COM_to_TARG x -> fTACTIC_COM x
| CT_coerce_TARG_LIST_to_TARG x -> fTARG_LIST x
| CT_coerce_UNFOLD_to_TARG x -> fUNFOLD x
| CT_coerce_UNFOLD_NE_LIST_to_TARG x -> fUNFOLD_NE_LIST x
and fTARG_LIST = function
| CT_targ_list l ->
   (List.fold_left (++) (mt()) (List.map fTARG l)) ++
   fNODE "targ_list" (List.length l)
and fTERM_CHANGE = function
| CT_check_term(x1) ->
   fFORMULA x1 ++
   fNODE "check_term" 1
| CT_inst_term(x1, x2) ->
   fID x1 ++
   fFORMULA x2 ++
   fNODE "inst_term" 2
and fTEXT = function
| CT_coerce_ID_to_TEXT x -> fID x
| CT_text_formula(x1) ->
   fFORMULA x1 ++
   fNODE "text_formula" 1
| CT_text_h l ->
   (List.fold_left (++) (mt()) (List.map fTEXT l)) ++
   fNODE "text_h" (List.length l)
| CT_text_hv l ->
   (List.fold_left (++) (mt()) (List.map fTEXT l)) ++
   fNODE "text_hv" (List.length l)
| CT_text_op l ->
   (List.fold_left (++) (mt()) (List.map fTEXT l)) ++
   fNODE "text_op" (List.length l)
| CT_text_path(x1) ->
   fSIGNED_INT_LIST x1 ++
   fNODE "text_path" 1
| CT_text_v l ->
   (List.fold_left (++) (mt()) (List.map fTEXT l)) ++
   fNODE "text_v" (List.length l)
and fTHEOREM_GOAL = function
| CT_goal(x1) ->
   fFORMULA x1 ++
   fNODE "goal" 1
| CT_theorem_goal(x1, x2, x3, x4) ->
   fDEFN_OR_THM x1 ++
   fID x2 ++
   fBINDER_LIST x3 ++
   fFORMULA x4 ++
   fNODE "theorem_goal" 4
and fTHM = function
| CT_thm x -> fATOM "thm" ++
   (f_atom_string x) ++
   str "\n"
and fTHM_OPT = function
| CT_coerce_NONE_to_THM_OPT x -> fNONE x
| CT_coerce_THM_to_THM_OPT x -> fTHM x
and fTYPED_FORMULA = function
| CT_typed_formula(x1, x2) ->
   fFORMULA x1 ++
   fFORMULA x2 ++
   fNODE "typed_formula" 2
and fUNFOLD = function
| CT_coerce_ID_to_UNFOLD x -> fID x
| CT_unfold_occ(x1, x2) ->
   fID x1 ++
   fINT_NE_LIST x2 ++
   fNODE "unfold_occ" 2
and fUNFOLD_NE_LIST = function
| CT_unfold_ne_list(x,l) ->
   fUNFOLD x ++
   (List.fold_left (++) (mt()) (List.map fUNFOLD l)) ++
   fNODE "unfold_ne_list" (1 + (List.length l))
and fUSING = function
| CT_coerce_NONE_to_USING x -> fNONE x
| CT_using(x1, x2) ->
   fFORMULA x1 ++
   fSPEC_LIST x2 ++
   fNODE "using" 2
and fUSINGTDB = function
| CT_coerce_NONE_to_USINGTDB x -> fNONE x
| CT_usingtdb -> fNODE "usingtdb" 0
and fVAR = function
| CT_var x -> fATOM "var" ++
   (f_atom_string x) ++
   str "\n"
and fVARG = function
| CT_coerce_AST_to_VARG x -> fAST x
| CT_coerce_AST_LIST_to_VARG x -> fAST_LIST x
| CT_coerce_BINDER_to_VARG x -> fBINDER x
| CT_coerce_BINDER_LIST_to_VARG x -> fBINDER_LIST x
| CT_coerce_BINDER_NE_LIST_to_VARG x -> fBINDER_NE_LIST x
| CT_coerce_FORMULA_LIST_to_VARG x -> fFORMULA_LIST x
| CT_coerce_FORMULA_OPT_to_VARG x -> fFORMULA_OPT x
| CT_coerce_FORMULA_OR_INT_to_VARG x -> fFORMULA_OR_INT x
| CT_coerce_ID_OPT_OR_ALL_to_VARG x -> fID_OPT_OR_ALL x
| CT_coerce_ID_OR_INT_OPT_to_VARG x -> fID_OR_INT_OPT x
| CT_coerce_INT_LIST_to_VARG x -> fINT_LIST x
| CT_coerce_SCOMMENT_CONTENT_to_VARG x -> fSCOMMENT_CONTENT x
| CT_coerce_STRING_OPT_to_VARG x -> fSTRING_OPT x
| CT_coerce_TACTIC_OPT_to_VARG x -> fTACTIC_OPT x
| CT_coerce_VARG_LIST_to_VARG x -> fVARG_LIST x
and fVARG_LIST = function
| CT_varg_list l ->
   (List.fold_left (++) (mt()) (List.map fVARG l)) ++
   fNODE "varg_list" (List.length l)
and fVERBOSE_OPT = function
| CT_coerce_NONE_to_VERBOSE_OPT x -> fNONE x
| CT_verbose -> fNODE "verbose" 0
;;
