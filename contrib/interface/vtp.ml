open Ascent;;

let fNODE s n =
    print_string "n\n";
    print_string ("vernac$" ^ s);
    print_string "\n";
    print_int n;
    print_string "\n";;

let fATOM s1 =
    print_string "a\n";
    print_string ("vernac$" ^ s1);
    print_string "\n";;

let f_atom_string = print_string;;
let f_atom_int = print_int;;
let rec fASSOC = function
| CT_coerce_NONE_to_ASSOC x -> fNONE x
| CT_lefta -> fNODE "lefta" 0
| CT_nona -> fNODE "nona" 0
| CT_righta -> fNODE "righta" 0
and fAST = function
| CT_coerce_ID_OR_INT_to_AST x -> fID_OR_INT x
| CT_coerce_ID_OR_STRING_to_AST x -> fID_OR_STRING x
| CT_astnode(x1, x2) ->
   fID x1;
   fAST_LIST x2;
   fNODE "astnode" 2
| CT_astpath(x1, x2) ->
   fID_LIST x1;
   fID x2;
   fNODE "astpath" 2
| CT_astslam(x1, x2) ->
   fID_OPT x1;
   fAST x2;
   fNODE "astslam" 2
and fAST_LIST = function
| CT_ast_list l ->
   (List.iter fAST l);
   fNODE "ast_list" (List.length l)
and fBINARY = function
| CT_binary x -> fATOM "binary";
   (f_atom_int x);
   print_string "\n"and fBINDER = function
| CT_binder(x1, x2) ->
   fID_OPT_NE_LIST x1;
   fFORMULA x2;
   fNODE "binder" 2
and fBINDER_LIST = function
| CT_binder_list l ->
   (List.iter fBINDER l);
   fNODE "binder_list" (List.length l)
and fBINDER_NE_LIST = function
| CT_binder_ne_list(x,l) ->
   fBINDER x;
   (List.iter fBINDER l);
   fNODE "binder_ne_list" (1 + (List.length l))
and fBINDING = function
| CT_binding(x1, x2) ->
   fID_OR_INT x1;
   fFORMULA x2;
   fNODE "binding" 2
and fBINDING_LIST = function
| CT_binding_list l ->
   (List.iter fBINDING l);
   fNODE "binding_list" (List.length l)
and fBOOL = function
| CT_false -> fNODE "false" 0
| CT_true -> fNODE "true" 0
and fCASE = function
| CT_case x -> fATOM "case";
   (f_atom_string x);
   print_string "\n"and fCOERCION_OPT = function
| CT_coerce_NONE_to_COERCION_OPT x -> fNONE x
| CT_coercion_atm -> fNODE "coercion_atm" 0
and fCOFIXTAC = function
| CT_cofixtac(x1, x2) ->
   fID x1;
   fFORMULA x2;
   fNODE "cofixtac" 2
and fCOFIX_REC = function
| CT_cofix_rec(x1, x2, x3) ->
   fID x1;
   fFORMULA x2;
   fFORMULA x3;
   fNODE "cofix_rec" 3
and fCOFIX_REC_LIST = function
| CT_cofix_rec_list(x,l) ->
   fCOFIX_REC x;
   (List.iter fCOFIX_REC l);
   fNODE "cofix_rec_list" (1 + (List.length l))
and fCOFIX_TAC_LIST = function
| CT_cofix_tac_list l ->
   (List.iter fCOFIXTAC l);
   fNODE "cofix_tac_list" (List.length l)
and fCOMMAND = function
| CT_coerce_COMMAND_LIST_to_COMMAND x -> fCOMMAND_LIST x
| CT_coerce_EVAL_CMD_to_COMMAND x -> fEVAL_CMD x
| CT_coerce_IMPEXP_to_COMMAND x -> fIMPEXP x
| CT_coerce_SECTION_BEGIN_to_COMMAND x -> fSECTION_BEGIN x
| CT_coerce_THEOREM_GOAL_to_COMMAND x -> fTHEOREM_GOAL x
| CT_abort(x1) ->
   fID_OPT_OR_ALL x1;
   fNODE "abort" 1
| CT_abstraction(x1, x2, x3) ->
   fID x1;
   fFORMULA x2;
   fINT_LIST x3;
   fNODE "abstraction" 3
| CT_add_natural_feature(x1, x2) ->
   fNATURAL_FEATURE x1;
   fID x2;
   fNODE "add_natural_feature" 2
| CT_addpath(x1) ->
   fSTRING x1;
   fNODE "addpath" 1
| CT_cd(x1) ->
   fSTRING_OPT x1;
   fNODE "cd" 1
| CT_check(x1) ->
   fFORMULA x1;
   fNODE "check" 1
| CT_class(x1) ->
   fID x1;
   fNODE "class" 1
| CT_coercion(x1, x2, x3, x4, x5) ->
   fLOCAL_OPT x1;
   fIDENTITY_OPT x2;
   fID x3;
   fID x4;
   fID x5;
   fNODE "coercion" 5
| CT_cofix_decl(x1) ->
   fCOFIX_REC_LIST x1;
   fNODE "cofix_decl" 1
| CT_compile_module(x1, x2, x3) ->
   fVERBOSE_OPT x1;
   fID x2;
   fSTRING_OPT x3;
   fNODE "compile_module" 3
| CT_definition(x1, x2, x3, x4) ->
   fDEFN x1;
   fID x2;
   fDEF_BODY x3;
   fFORMULA_OPT x4;
   fNODE "definition" 4
| CT_delpath(x1) ->
   fSTRING x1;
   fNODE "delpath" 1
| CT_derive_depinversion(x1, x2, x3, x4) ->
   fINV_TYPE x1;
   fID x2;
   fFORMULA x3;
   fSORT_TYPE x4;
   fNODE "derive_depinversion" 4
| CT_derive_inversion(x1, x2, x3, x4) ->
   fINV_TYPE x1;
   fINT_OPT x2;
   fID x3;
   fID x4;
   fNODE "derive_inversion" 4
| CT_derive_inversion_with(x1, x2, x3, x4) ->
   fINV_TYPE x1;
   fID x2;
   fFORMULA x3;
   fSORT_TYPE x4;
   fNODE "derive_inversion_with" 4
| CT_explain_proof(x1) ->
   fINT_LIST x1;
   fNODE "explain_proof" 1
| CT_explain_prooftree(x1) ->
   fINT_LIST x1;
   fNODE "explain_prooftree" 1
| CT_fix_decl(x1) ->
   fFIX_REC_LIST x1;
   fNODE "fix_decl" 1
| CT_focus(x1) ->
   fINT_OPT x1;
   fNODE "focus" 1
| CT_go(x1) ->
   fINT_OR_LOCN x1;
   fNODE "go" 1
| CT_guarded -> fNODE "guarded" 0
| CT_hint(x1, x2, x3) ->
   fID x1;
   fID_LIST x2;
   fHINT_EXPRESSION x3;
   fNODE "hint" 3
| CT_hintrewrite(x1, x2, x3, x4) ->
   fORIENTATION x1;
   fFORMULA_NE_LIST x2;
   fID x3;
   fTACTIC_COM x4;
   fNODE "hintrewrite" 4
| CT_hints(x1, x2, x3) ->
   fID x1;
   fID_NE_LIST x2;
   fID_LIST x3;
   fNODE "hints" 3
| CT_ind_scheme(x1) ->
   fSCHEME_SPEC_LIST x1;
   fNODE "ind_scheme" 1
| CT_infix(x1, x2, x3, x4) ->
   fASSOC x1;
   fINT x2;
   fSTRING x3;
   fID x4;
   fNODE "infix" 4
| CT_inspect(x1) ->
   fINT x1;
   fNODE "inspect" 1
| CT_kill_node(x1) ->
   fINT x1;
   fNODE "kill_node" 1
| CT_load(x1, x2) ->
   fVERBOSE_OPT x1;
   fID_OR_STRING x2;
   fNODE "load" 2
| CT_mind_decl(x1, x2) ->
   fCO_IND x1;
   fIND_SPEC_LIST x2;
   fNODE "mind_decl" 2
| CT_ml_add_path(x1) ->
   fSTRING x1;
   fNODE "ml_add_path" 1
| CT_ml_declare_modules(x1) ->
   fSTRING_NE_LIST x1;
   fNODE "ml_declare_modules" 1
| CT_ml_print_modules -> fNODE "ml_print_modules" 0
| CT_ml_print_path -> fNODE "ml_print_path" 0
| CT_module(x1) ->
   fID x1;
   fNODE "module" 1
| CT_omega_flag(x1, x2) ->
   fOMEGA_MODE x1;
   fOMEGA_FEATURE x2;
   fNODE "omega_flag" 2
| CT_opaque(x1) ->
   fID_NE_LIST x1;
   fNODE "opaque" 1
| CT_parameter(x1) ->
   fBINDER x1;
   fNODE "parameter" 1
| CT_print_all -> fNODE "print_all" 0
| CT_print_classes -> fNODE "print_classes" 0
| CT_print_coercions -> fNODE "print_coercions" 0
| CT_print_grammar(x1) ->
   fGRAMMAR x1;
   fNODE "print_grammar" 1
| CT_print_graph -> fNODE "print_graph" 0
| CT_print_hint(x1) ->
   fID_OPT x1;
   fNODE "print_hint" 1
| CT_print_hintdb(x1) ->
   fID x1;
   fNODE "print_hintdb" 1
| CT_print_id(x1) ->
   fID x1;
   fNODE "print_id" 1
| CT_print_loadpath -> fNODE "print_loadpath" 0
| CT_print_modules -> fNODE "print_modules" 0
| CT_print_natural(x1) ->
   fID x1;
   fNODE "print_natural" 1
| CT_print_natural_feature(x1) ->
   fNATURAL_FEATURE x1;
   fNODE "print_natural_feature" 1
| CT_print_opaqueid(x1) ->
   fID x1;
   fNODE "print_opaqueid" 1
| CT_print_path(x1, x2) ->
   fID x1;
   fID x2;
   fNODE "print_path" 2
| CT_print_proof(x1) ->
   fID x1;
   fNODE "print_proof" 1
| CT_print_section(x1) ->
   fID x1;
   fNODE "print_section" 1
| CT_print_states -> fNODE "print_states" 0
| CT_proof(x1) ->
   fFORMULA x1;
   fNODE "proof" 1
| CT_proof_no_op -> fNODE "proof_no_op" 0
| CT_pwd -> fNODE "pwd" 0
| CT_quit -> fNODE "quit" 0
| CT_read_module(x1) ->
   fID x1;
   fNODE "read_module" 1
| CT_rec_ml_add_path(x1) ->
   fSTRING x1;
   fNODE "rec_ml_add_path" 1
| CT_rec_tactic_definition(x1) ->
   fREC_TACTIC_FUN_LIST x1;
   fNODE "rec_tactic_definition" 1
| CT_recaddpath(x1) ->
   fSTRING x1;
   fNODE "recaddpath" 1
| CT_record(x1, x2, x3, x4, x5, x6) ->
   fCOERCION_OPT x1;
   fID x2;
   fBINDER_LIST x3;
   fSORT_TYPE x4;
   fID_OPT x5;
   fRECCONSTR_LIST x6;
   fNODE "record" 6
| CT_remove_natural_feature(x1, x2) ->
   fNATURAL_FEATURE x1;
   fID x2;
   fNODE "remove_natural_feature" 2
| CT_require(x1, x2, x3, x4) ->
   fIMPEXP x1;
   fSPEC_OPT x2;
   fID x3;
   fSTRING_OPT x4;
   fNODE "require" 4
| CT_reset(x1) ->
   fID x1;
   fNODE "reset" 1
| CT_reset_section(x1) ->
   fID x1;
   fNODE "reset_section" 1
| CT_restart -> fNODE "restart" 0
| CT_restore_state(x1) ->
   fID x1;
   fNODE "restore_state" 1
| CT_resume(x1) ->
   fID_OPT x1;
   fNODE "resume" 1
| CT_save(x1, x2) ->
   fTHM_OPT x1;
   fID_OPT x2;
   fNODE "save" 2
| CT_search(x1, x2) ->
   fID x1;
   fIN_OR_OUT_MODULES x2;
   fNODE "search" 2
| CT_search_pattern(x1, x2) ->
   fFORMULA x1;
   fIN_OR_OUT_MODULES x2;
   fNODE "search_pattern" 2
| CT_search_rewrite(x1, x2) ->
   fFORMULA x1;
   fIN_OR_OUT_MODULES x2;
   fNODE "search_rewrite" 2
| CT_section_end(x1) ->
   fID x1;
   fNODE "section_end" 1
| CT_section_struct(x1, x2, x3) ->
   fSECTION_BEGIN x1;
   fSECTION_BODY x2;
   fCOMMAND x3;
   fNODE "section_struct" 3
| CT_set_natural(x1) ->
   fID x1;
   fNODE "set_natural" 1
| CT_set_natural_default -> fNODE "set_natural_default" 0
| CT_sethyp(x1) ->
   fINT x1;
   fNODE "sethyp" 1
| CT_setundo(x1) ->
   fINT x1;
   fNODE "setundo" 1
| CT_show_goal(x1) ->
   fINT_OPT x1;
   fNODE "show_goal" 1
| CT_show_implicits -> fNODE "show_implicits" 0
| CT_show_node -> fNODE "show_node" 0
| CT_show_proof -> fNODE "show_proof" 0
| CT_show_proofs -> fNODE "show_proofs" 0
| CT_show_script -> fNODE "show_script" 0
| CT_show_tree -> fNODE "show_tree" 0
| CT_solve(x1, x2) ->
   fINT x1;
   fTACTIC_COM x2;
   fNODE "solve" 2
| CT_suspend -> fNODE "suspend" 0
| CT_syntax_macro(x1, x2, x3) ->
   fID x1;
   fFORMULA x2;
   fINT_OPT x3;
   fNODE "syntax_macro" 3
| CT_tactic_definition(x1, x2, x3) ->
   fID x1;
   fID_LIST x2;
   fTACTIC_COM x3;
   fNODE "tactic_definition" 3
| CT_test_natural_feature(x1, x2) ->
   fNATURAL_FEATURE x1;
   fID x2;
   fNODE "test_natural_feature" 2
| CT_theorem_struct(x1, x2) ->
   fTHEOREM_GOAL x1;
   fPROOF_SCRIPT x2;
   fNODE "theorem_struct" 2
| CT_token(x1) ->
   fSTRING x1;
   fNODE "token" 1
| CT_transparent(x1) ->
   fID_NE_LIST x1;
   fNODE "transparent" 1
| CT_undo(x1) ->
   fINT_OPT x1;
   fNODE "undo" 1
| CT_unfocus -> fNODE "unfocus" 0
| CT_unsethyp -> fNODE "unsethyp" 0
| CT_unsetundo -> fNODE "unsetundo" 0
| CT_user_vernac(x1, x2) ->
   fID x1;
   fVARG_LIST x2;
   fNODE "user_vernac" 2
| CT_variable(x1, x2) ->
   fVAR x1;
   fBINDER_LIST x2;
   fNODE "variable" 2
| CT_write_module(x1, x2) ->
   fID x1;
   fSTRING_OPT x2;
   fNODE "write_module" 2
and fCOMMAND_LIST = function
| CT_command_list(x,l) ->
   fCOMMAND x;
   (List.iter fCOMMAND l);
   fNODE "command_list" (1 + (List.length l))
and fCOMMENT = function
| CT_comment x -> fATOM "comment";
   (f_atom_string x);
   print_string "\n"and fCOMMENT_S = function
| CT_comment_s l ->
   (List.iter fCOMMENT l);
   fNODE "comment_s" (List.length l)
and fCONSTR = function
| CT_constr(x1, x2) ->
   fID x1;
   fFORMULA x2;
   fNODE "constr" 2
and fCONSTR_LIST = function
| CT_constr_list l ->
   (List.iter fCONSTR l);
   fNODE "constr_list" (List.length l)
and fCONTEXT_HYP_LIST = function
| CT_context_hyp_list l ->
   (List.iter fPREMISE_PATTERN l);
   fNODE "context_hyp_list" (List.length l)
and fCONTEXT_PATTERN = function
| CT_coerce_FORMULA_to_CONTEXT_PATTERN x -> fFORMULA x
| CT_context(x1, x2) ->
   fID_OPT x1;
   fFORMULA x2;
   fNODE "context" 2
and fCONTEXT_RULE = function
| CT_context_rule(x1, x2, x3) ->
   fCONTEXT_HYP_LIST x1;
   fCONTEXT_PATTERN x2;
   fTACTIC_COM x3;
   fNODE "context_rule" 3
and fCONVERSION_FLAG = function
| CT_beta -> fNODE "beta" 0
| CT_delta -> fNODE "delta" 0
| CT_iota -> fNODE "iota" 0
and fCONVERSION_FLAG_LIST = function
| CT_conversion_flag_list l ->
   (List.iter fCONVERSION_FLAG l);
   fNODE "conversion_flag_list" (List.length l)
and fCONV_SET = function
| CT_unf l ->
   (List.iter fID l);
   fNODE "unf" (List.length l)
| CT_unfbut l ->
   (List.iter fID l);
   fNODE "unfbut" (List.length l)
and fCO_IND = function
| CT_co_ind x -> fATOM "co_ind";
   (f_atom_string x);
   print_string "\n"and fDEFN = function
| CT_defn x -> fATOM "defn";
   (f_atom_string x);
   print_string "\n"and fDEFN_OR_THM = function
| CT_coerce_DEFN_to_DEFN_OR_THM x -> fDEFN x
| CT_coerce_THM_to_DEFN_OR_THM x -> fTHM x
and fDEF_BODY = function
| CT_coerce_EVAL_CMD_to_DEF_BODY x -> fEVAL_CMD x
| CT_coerce_FORMULA_to_DEF_BODY x -> fFORMULA x
and fDEP = function
| CT_dep x -> fATOM "dep";
   (f_atom_string x);
   print_string "\n"and fDESTRUCTING = function
| CT_coerce_NONE_to_DESTRUCTING x -> fNONE x
| CT_destructing -> fNODE "destructing" 0
and fEQN = function
| CT_eqn(x1, x2) ->
   fMATCH_PATTERN_NE_LIST x1;
   fFORMULA x2;
   fNODE "eqn" 2
and fEQN_LIST = function
| CT_eqn_list l ->
   (List.iter fEQN l);
   fNODE "eqn_list" (List.length l)
and fEVAL_CMD = function
| CT_eval(x1, x2, x3) ->
   fINT_OPT x1;
   fRED_COM x2;
   fFORMULA x3;
   fNODE "eval" 3
and fFIXTAC = function
| CT_fixtac(x1, x2, x3) ->
   fID x1;
   fINT x2;
   fFORMULA x3;
   fNODE "fixtac" 3
and fFIX_BINDER = function
| CT_coerce_FIX_REC_to_FIX_BINDER x -> fFIX_REC x
| CT_fix_binder(x1, x2, x3, x4) ->
   fID x1;
   fINT x2;
   fFORMULA x3;
   fFORMULA x4;
   fNODE "fix_binder" 4
and fFIX_BINDER_LIST = function
| CT_fix_binder_list(x,l) ->
   fFIX_BINDER x;
   (List.iter fFIX_BINDER l);
   fNODE "fix_binder_list" (1 + (List.length l))
and fFIX_REC = function
| CT_fix_rec(x1, x2, x3, x4) ->
   fID x1;
   fBINDER_NE_LIST x2;
   fFORMULA x3;
   fFORMULA x4;
   fNODE "fix_rec" 4
and fFIX_REC_LIST = function
| CT_fix_rec_list(x,l) ->
   fFIX_REC x;
   (List.iter fFIX_REC l);
   fNODE "fix_rec_list" (1 + (List.length l))
and fFIX_TAC_LIST = function
| CT_fix_tac_list l ->
   (List.iter fFIXTAC l);
   fNODE "fix_tac_list" (List.length l)
and fFORMULA = function
| CT_coerce_BINARY_to_FORMULA x -> fBINARY x
| CT_coerce_ID_to_FORMULA x -> fID x
| CT_coerce_SORT_TYPE_to_FORMULA x -> fSORT_TYPE x
| CT_coerce_TYPED_FORMULA_to_FORMULA x -> fTYPED_FORMULA x
| CT_appc(x1, x2) ->
   fFORMULA x1;
   fFORMULA_NE_LIST x2;
   fNODE "appc" 2
| CT_arrowc(x1, x2) ->
   fFORMULA x1;
   fFORMULA x2;
   fNODE "arrowc" 2
| CT_bang(x1, x2) ->
   fINT_OPT x1;
   fFORMULA x2;
   fNODE "bang" 2
| CT_cases(x1, x2, x3) ->
   fFORMULA_OPT x1;
   fFORMULA_NE_LIST x2;
   fEQN_LIST x3;
   fNODE "cases" 3
| CT_cofixc(x1, x2) ->
   fID x1;
   fCOFIX_REC_LIST x2;
   fNODE "cofixc" 2
| CT_elimc(x1, x2, x3, x4) ->
   fCASE x1;
   fFORMULA x2;
   fFORMULA x3;
   fFORMULA_LIST x4;
   fNODE "elimc" 4
| CT_existvarc -> fNODE "existvarc" 0
| CT_fixc(x1, x2) ->
   fID x1;
   fFIX_BINDER_LIST x2;
   fNODE "fixc" 2
| CT_incomplete_binary(x1, x2) ->
   fFORMULA x1;
   fBINARY x2;
   fNODE "incomplete_binary" 2
| CT_int_encapsulator(x1) ->
   fINT x1;
   fNODE "int_encapsulator" 1
| CT_lambdac(x1, x2) ->
   fBINDER x1;
   fFORMULA x2;
   fNODE "lambdac" 2
| CT_letin(x1, x2, x3) ->
   fID x1;
   fFORMULA x2;
   fFORMULA x3;
   fNODE "letin" 3
| CT_metac(x1) ->
   fINT x1;
   fNODE "metac" 1
| CT_prodc(x1, x2) ->
   fBINDER x1;
   fFORMULA x2;
   fNODE "prodc" 2
and fFORMULA_LIST = function
| CT_formula_list l ->
   (List.iter fFORMULA l);
   fNODE "formula_list" (List.length l)
and fFORMULA_NE_LIST = function
| CT_formula_ne_list(x,l) ->
   fFORMULA x;
   (List.iter fFORMULA l);
   fNODE "formula_ne_list" (1 + (List.length l))
and fFORMULA_OPT = function
| CT_coerce_FORMULA_to_FORMULA_OPT x -> fFORMULA x
| CT_coerce_ID_OPT_to_FORMULA_OPT x -> fID_OPT x
and fGRAMMAR = function
| CT_grammar_none -> fNODE "grammar_none" 0
and fHINT_EXPRESSION = function
| CT_constructors(x1) ->
   fID x1;
   fNODE "constructors" 1
| CT_extern(x1, x2, x3) ->
   fINT x1;
   fFORMULA x2;
   fTACTIC_COM x3;
   fNODE "extern" 3
| CT_immediate(x1) ->
   fFORMULA x1;
   fNODE "immediate" 1
| CT_resolve(x1) ->
   fFORMULA x1;
   fNODE "resolve" 1
| CT_unfold_hint(x1) ->
   fID x1;
   fNODE "unfold_hint" 1
and fID = function
| CT_ident x -> fATOM "ident";
   (f_atom_string x);
   print_string "\n"and fIDENTITY_OPT = function
| CT_coerce_NONE_to_IDENTITY_OPT x -> fNONE x
| CT_identity -> fNODE "identity" 0
and fID_LIST = function
| CT_id_list l ->
   (List.iter fID l);
   fNODE "id_list" (List.length l)
and fID_NE_LIST = function
| CT_id_ne_list(x,l) ->
   fID x;
   (List.iter fID l);
   fNODE "id_ne_list" (1 + (List.length l))
and fID_NE_LIST_OR_STAR = function
| CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR x -> fID_NE_LIST x
| CT_star -> fNODE "star" 0
and fID_OPT = function
| CT_coerce_ID_to_ID_OPT x -> fID x
| CT_coerce_NONE_to_ID_OPT x -> fNONE x
and fID_OPT_NE_LIST = function
| CT_id_opt_ne_list(x,l) ->
   fID_OPT x;
   (List.iter fID_OPT l);
   fNODE "id_opt_ne_list" (1 + (List.length l))
and fID_OPT_OR_ALL = function
| CT_coerce_ID_OPT_to_ID_OPT_OR_ALL x -> fID_OPT x
| CT_all -> fNODE "all" 0
and fID_OR_INT = function
| CT_coerce_ID_to_ID_OR_INT x -> fID x
| CT_coerce_INT_to_ID_OR_INT x -> fINT x
and fID_OR_STRING = function
| CT_coerce_ID_to_ID_OR_STRING x -> fID x
| CT_coerce_STRING_to_ID_OR_STRING x -> fSTRING x
and fID_UNIT = function
| CT_coerce_ID_to_ID_UNIT x -> fID x
| CT_unit -> fNODE "unit" 0
and fID_UNIT_LIST = function
| CT_id_unit_list(x,l) ->
   fID_UNIT x;
   (List.iter fID_UNIT l);
   fNODE "id_unit_list" (1 + (List.length l))
and fIMPEXP = function
| CT_export -> fNODE "export" 0
| CT_import -> fNODE "import" 0
and fIND_SPEC = function
| CT_ind_spec(x1, x2, x3, x4) ->
   fID x1;
   fBINDER_LIST x2;
   fFORMULA x3;
   fCONSTR_LIST x4;
   fNODE "ind_spec" 4
and fIND_SPEC_LIST = function
| CT_ind_spec_list l ->
   (List.iter fIND_SPEC l);
   fNODE "ind_spec_list" (List.length l)
and fINT = function
| CT_int x -> fATOM "int";
   (f_atom_int x);
   print_string "\n"and fINTRO_PATT = function
| CT_coerce_ID_to_INTRO_PATT x -> fID x
| CT_conj_pattern(x1) ->
   fINTRO_PATT_LIST x1;
   fNODE "conj_pattern" 1
| CT_disj_pattern(x1) ->
   fINTRO_PATT_LIST x1;
   fNODE "disj_pattern" 1
and fINTRO_PATT_LIST = function
| CT_intro_patt_list l ->
   (List.iter fINTRO_PATT l);
   fNODE "intro_patt_list" (List.length l)
and fINT_LIST = function
| CT_int_list l ->
   (List.iter fINT l);
   fNODE "int_list" (List.length l)
and fINT_NE_LIST = function
| CT_int_ne_list(x,l) ->
   fINT x;
   (List.iter fINT l);
   fNODE "int_ne_list" (1 + (List.length l))
and fINT_OPT = function
| CT_coerce_INT_to_INT_OPT x -> fINT x
| CT_coerce_NONE_to_INT_OPT x -> fNONE x
and fINT_OR_LOCN = function
| CT_coerce_INT_to_INT_OR_LOCN x -> fINT x
| CT_coerce_LOCN_to_INT_OR_LOCN x -> fLOCN x
and fINV_TYPE = function
| CT_inv_clear -> fNODE "inv_clear" 0
| CT_inv_regular -> fNODE "inv_regular" 0
| CT_inv_simple -> fNODE "inv_simple" 0
and fIN_OR_OUT_MODULES = function
| CT_coerce_NONE_to_IN_OR_OUT_MODULES x -> fNONE x
| CT_in_modules(x1) ->
   fID_NE_LIST x1;
   fNODE "in_modules" 1
| CT_out_modules(x1) ->
   fID_NE_LIST x1;
   fNODE "out_modules" 1
and fLOCAL_OPT = function
| CT_coerce_NONE_to_LOCAL_OPT x -> fNONE x
| CT_local -> fNODE "local" 0
and fLOCN = function
| CT_locn x -> fATOM "locn";
   (f_atom_string x);
   print_string "\n"and fMATCH_PATTERN = function
| CT_coerce_ID_OPT_to_MATCH_PATTERN x -> fID_OPT x
| CT_pattern_app(x1, x2) ->
   fMATCH_PATTERN x1;
   fMATCH_PATTERN_NE_LIST x2;
   fNODE "pattern_app" 2
| CT_pattern_as(x1, x2) ->
   fMATCH_PATTERN x1;
   fID_OPT x2;
   fNODE "pattern_as" 2
and fMATCH_PATTERN_NE_LIST = function
| CT_match_pattern_ne_list(x,l) ->
   fMATCH_PATTERN x;
   (List.iter fMATCH_PATTERN l);
   fNODE "match_pattern_ne_list" (1 + (List.length l))
and fNATURAL_FEATURE = function
| CT_contractible -> fNODE "contractible" 0
| CT_implicit -> fNODE "implicit" 0
| CT_nat_transparent -> fNODE "nat_transparent" 0
and fNONE = function
| CT_none -> fNODE "none" 0
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
   fINT_LIST x1;
   fFORMULA x2;
   fNODE "pattern_occ" 2
and fPATTERN_NE_LIST = function
| CT_pattern_ne_list(x,l) ->
   fPATTERN x;
   (List.iter fPATTERN l);
   fNODE "pattern_ne_list" (1 + (List.length l))
and fPREMISE = function
| CT_coerce_TYPED_FORMULA_to_PREMISE x -> fTYPED_FORMULA x
| CT_eval_result(x1, x2, x3) ->
   fFORMULA x1;
   fFORMULA x2;
   fFORMULA x3;
   fNODE "eval_result" 3
| CT_premise(x1, x2) ->
   fID x1;
   fFORMULA x2;
   fNODE "premise" 2
and fPREMISES_LIST = function
| CT_premises_list l ->
   (List.iter fPREMISE l);
   fNODE "premises_list" (List.length l)
and fPREMISE_PATTERN = function
| CT_premise_pattern(x1, x2) ->
   fID_OPT x1;
   fCONTEXT_PATTERN x2;
   fNODE "premise_pattern" 2
and fPROOF_SCRIPT = function
| CT_proof_script l ->
   (List.iter fCOMMAND l);
   fNODE "proof_script" (List.length l)
and fRECCONSTR = function
| CT_coerce_CONSTR_to_RECCONSTR x -> fCONSTR x
| CT_constr_coercion(x1, x2) ->
   fID x1;
   fFORMULA x2;
   fNODE "constr_coercion" 2
and fRECCONSTR_LIST = function
| CT_recconstr_list l ->
   (List.iter fRECCONSTR l);
   fNODE "recconstr_list" (List.length l)
and fREC_TACTIC_FUN = function
| CT_rec_tactic_fun(x1, x2, x3) ->
   fID x1;
   fID_UNIT_LIST x2;
   fTACTIC_COM x3;
   fNODE "rec_tactic_fun" 3
and fREC_TACTIC_FUN_LIST = function
| CT_rec_tactic_fun_list(x,l) ->
   fREC_TACTIC_FUN x;
   (List.iter fREC_TACTIC_FUN l);
   fNODE "rec_tactic_fun_list" (1 + (List.length l))
and fRED_COM = function
| CT_cbv(x1, x2) ->
   fCONVERSION_FLAG_LIST x1;
   fCONV_SET x2;
   fNODE "cbv" 2
| CT_fold(x1) ->
   fFORMULA_LIST x1;
   fNODE "fold" 1
| CT_hnf -> fNODE "hnf" 0
| CT_lazy(x1, x2) ->
   fCONVERSION_FLAG_LIST x1;
   fCONV_SET x2;
   fNODE "lazy" 2
| CT_pattern(x1) ->
   fPATTERN_NE_LIST x1;
   fNODE "pattern" 1
| CT_red -> fNODE "red" 0
| CT_simpl -> fNODE "simpl" 0
| CT_unfold(x1) ->
   fUNFOLD_NE_LIST x1;
   fNODE "unfold" 1
and fRULE = function
| CT_rule(x1, x2) ->
   fPREMISES_LIST x1;
   fFORMULA x2;
   fNODE "rule" 2
and fRULE_LIST = function
| CT_rule_list l ->
   (List.iter fRULE l);
   fNODE "rule_list" (List.length l)
and fSCHEME_SPEC = function
| CT_scheme_spec(x1, x2, x3, x4) ->
   fID x1;
   fDEP x2;
   fFORMULA x3;
   fSORT_TYPE x4;
   fNODE "scheme_spec" 4
and fSCHEME_SPEC_LIST = function
| CT_scheme_spec_list(x,l) ->
   fSCHEME_SPEC x;
   (List.iter fSCHEME_SPEC l);
   fNODE "scheme_spec_list" (1 + (List.length l))
and fSECTION_BEGIN = function
| CT_section(x1) ->
   fID x1;
   fNODE "section" 1
and fSECTION_BODY = function
| CT_section_body l ->
   (List.iter fCOMMAND l);
   fNODE "section_body" (List.length l)
and fSIGNED_INT = function
| CT_coerce_INT_to_SIGNED_INT x -> fINT x
| CT_minus(x1) ->
   fINT x1;
   fNODE "minus" 1
and fSIGNED_INT_LIST = function
| CT_signed_int_list l ->
   (List.iter fSIGNED_INT l);
   fNODE "signed_int_list" (List.length l)
and fSORT_TYPE = function
| CT_sortc x -> fATOM "sortc";
   (f_atom_string x);
   print_string "\n"and fSPEC_LIST = function
| CT_coerce_BINDING_LIST_to_SPEC_LIST x -> fBINDING_LIST x
| CT_coerce_FORMULA_LIST_to_SPEC_LIST x -> fFORMULA_LIST x
and fSPEC_OPT = function
| CT_coerce_NONE_to_SPEC_OPT x -> fNONE x
| CT_spec -> fNODE "spec" 0
and fSTRING = function
| CT_string x -> fATOM "string";
   (f_atom_string x);
   print_string "\n"and fSTRING_NE_LIST = function
| CT_string_ne_list(x,l) ->
   fSTRING x;
   (List.iter fSTRING l);
   fNODE "string_ne_list" (1 + (List.length l))
and fSTRING_OPT = function
| CT_coerce_NONE_to_STRING_OPT x -> fNONE x
| CT_coerce_STRING_to_STRING_OPT x -> fSTRING x
and fTACTIC_ARG = function
| CT_coerce_FORMULA_to_TACTIC_ARG x -> fFORMULA x
| CT_coerce_ID_OR_INT_to_TACTIC_ARG x -> fID_OR_INT x
| CT_coerce_TACTIC_COM_to_TACTIC_ARG x -> fTACTIC_COM x
| CT_void -> fNODE "void" 0
and fTACTIC_ARG_LIST = function
| CT_tactic_arg_list(x,l) ->
   fTACTIC_ARG x;
   (List.iter fTACTIC_ARG l);
   fNODE "tactic_arg_list" (1 + (List.length l))
and fTACTIC_COM = function
| CT_abstract(x1, x2) ->
   fID_OPT x1;
   fTACTIC_COM x2;
   fNODE "abstract" 2
| CT_absurd(x1) ->
   fFORMULA x1;
   fNODE "absurd" 1
| CT_apply(x1, x2) ->
   fFORMULA x1;
   fSPEC_LIST x2;
   fNODE "apply" 2
| CT_assumption -> fNODE "assumption" 0
| CT_auto(x1) ->
   fINT_OPT x1;
   fNODE "auto" 1
| CT_auto_with(x1, x2) ->
   fINT_OPT x1;
   fID_NE_LIST_OR_STAR x2;
   fNODE "auto_with" 2
| CT_autorewrite(x1, x2) ->
   fID_NE_LIST x1;
   fTACTIC_OPT x2;
   fNODE "autorewrite" 2
| CT_autotdb(x1) ->
   fINT_OPT x1;
   fNODE "autotdb" 1
| CT_case_type(x1) ->
   fFORMULA x1;
   fNODE "case_type" 1
| CT_casetac(x1, x2) ->
   fFORMULA x1;
   fSPEC_LIST x2;
   fNODE "casetac" 2
| CT_cdhyp(x1) ->
   fID x1;
   fNODE "cdhyp" 1
| CT_change(x1, x2) ->
   fFORMULA x1;
   fID_LIST x2;
   fNODE "change" 2
| CT_clear(x1) ->
   fID_NE_LIST x1;
   fNODE "clear" 1
| CT_cofixtactic(x1, x2) ->
   fID_OPT x1;
   fCOFIX_TAC_LIST x2;
   fNODE "cofixtactic" 2
| CT_condrewrite_lr(x1, x2, x3, x4) ->
   fTACTIC_COM x1;
   fFORMULA x2;
   fSPEC_LIST x3;
   fID_OPT x4;
   fNODE "condrewrite_lr" 4
| CT_condrewrite_rl(x1, x2, x3, x4) ->
   fTACTIC_COM x1;
   fFORMULA x2;
   fSPEC_LIST x3;
   fID_OPT x4;
   fNODE "condrewrite_rl" 4
| CT_constructor(x1, x2) ->
   fINT x1;
   fSPEC_LIST x2;
   fNODE "constructor" 2
| CT_contradiction -> fNODE "contradiction" 0
| CT_cut(x1) ->
   fFORMULA x1;
   fNODE "cut" 1
| CT_cutrewrite_lr(x1, x2) ->
   fFORMULA x1;
   fID_OPT x2;
   fNODE "cutrewrite_lr" 2
| CT_cutrewrite_rl(x1, x2) ->
   fFORMULA x1;
   fID_OPT x2;
   fNODE "cutrewrite_rl" 2
| CT_dconcl -> fNODE "dconcl" 0
| CT_decompose_list(x1, x2) ->
   fID_NE_LIST x1;
   fFORMULA x2;
   fNODE "decompose_list" 2
| CT_depinversion(x1, x2, x3) ->
   fINV_TYPE x1;
   fID x2;
   fFORMULA_OPT x3;
   fNODE "depinversion" 3
| CT_deprewrite_lr(x1) ->
   fID x1;
   fNODE "deprewrite_lr" 1
| CT_deprewrite_rl(x1) ->
   fID x1;
   fNODE "deprewrite_rl" 1
| CT_destruct(x1) ->
   fID_OR_INT x1;
   fNODE "destruct" 1
| CT_dhyp(x1) ->
   fID x1;
   fNODE "dhyp" 1
| CT_discriminate_eq(x1) ->
   fID_OPT x1;
   fNODE "discriminate_eq" 1
| CT_do(x1, x2) ->
   fINT x1;
   fTACTIC_COM x2;
   fNODE "do" 2
| CT_eapply(x1, x2) ->
   fFORMULA x1;
   fSPEC_LIST x2;
   fNODE "eapply" 2
| CT_eauto(x1) ->
   fINT_OPT x1;
   fNODE "eauto" 1
| CT_eauto_with(x1, x2) ->
   fINT_OPT x1;
   fID_NE_LIST_OR_STAR x2;
   fNODE "eauto_with" 2
| CT_elim(x1, x2, x3) ->
   fFORMULA x1;
   fSPEC_LIST x2;
   fUSING x3;
   fNODE "elim" 3
| CT_elim_type(x1) ->
   fFORMULA x1;
   fNODE "elim_type" 1
| CT_exact(x1) ->
   fFORMULA x1;
   fNODE "exact" 1
| CT_exists(x1) ->
   fSPEC_LIST x1;
   fNODE "exists" 1
| CT_fail -> fNODE "fail" 0
| CT_first(x,l) ->
   fTACTIC_COM x;
   (List.iter fTACTIC_COM l);
   fNODE "first" (1 + (List.length l))
| CT_fixtactic(x1, x2, x3) ->
   fID_OPT x1;
   fINT x2;
   fFIX_TAC_LIST x3;
   fNODE "fixtactic" 3
| CT_generalize(x1) ->
   fFORMULA_NE_LIST x1;
   fNODE "generalize" 1
| CT_generalize_dependent(x1) ->
   fFORMULA x1;
   fNODE "generalize_dependent" 1
| CT_idtac -> fNODE "idtac" 0
| CT_induction(x1) ->
   fID_OR_INT x1;
   fNODE "induction" 1
| CT_info(x1) ->
   fTACTIC_COM x1;
   fNODE "info" 1
| CT_injection_eq(x1) ->
   fID_OPT x1;
   fNODE "injection_eq" 1
| CT_intro(x1) ->
   fID_OPT x1;
   fNODE "intro" 1
| CT_intro_after(x1, x2) ->
   fID_OPT x1;
   fID x2;
   fNODE "intro_after" 2
| CT_intros(x1) ->
   fINTRO_PATT_LIST x1;
   fNODE "intros" 1
| CT_intros_until(x1) ->
   fID x1;
   fNODE "intros_until" 1
| CT_inversion(x1, x2, x3) ->
   fINV_TYPE x1;
   fID x2;
   fID_LIST x3;
   fNODE "inversion" 3
| CT_left(x1) ->
   fSPEC_LIST x1;
   fNODE "left" 1
| CT_lettac(x1, x2, x3) ->
   fID x1;
   fFORMULA x2;
   fUNFOLD_NE_LIST x3;
   fNODE "lettac" 3
| CT_match_context(x,l) ->
   fCONTEXT_RULE x;
   (List.iter fCONTEXT_RULE l);
   fNODE "match_context" (1 + (List.length l))
| CT_move_after(x1, x2) ->
   fID x1;
   fID x2;
   fNODE "move_after" 2
| CT_omega -> fNODE "omega" 0
| CT_orelse(x1, x2) ->
   fTACTIC_COM x1;
   fTACTIC_COM x2;
   fNODE "orelse" 2
| CT_parallel(x,l) ->
   fTACTIC_COM x;
   (List.iter fTACTIC_COM l);
   fNODE "parallel" (1 + (List.length l))
| CT_prolog(x1, x2) ->
   fFORMULA_LIST x1;
   fINT x2;
   fNODE "prolog" 2
| CT_rec_tactic_in(x1, x2) ->
   fREC_TACTIC_FUN_LIST x1;
   fTACTIC_COM x2;
   fNODE "rec_tactic_in" 2
| CT_reduce(x1, x2) ->
   fRED_COM x1;
   fID_LIST x2;
   fNODE "reduce" 2
| CT_reflexivity -> fNODE "reflexivity" 0
| CT_repeat(x1) ->
   fTACTIC_COM x1;
   fNODE "repeat" 1
| CT_replace_with(x1, x2) ->
   fFORMULA x1;
   fFORMULA x2;
   fNODE "replace_with" 2
| CT_rewrite_lr(x1, x2, x3) ->
   fFORMULA x1;
   fSPEC_LIST x2;
   fID_OPT x3;
   fNODE "rewrite_lr" 3
| CT_rewrite_rl(x1, x2, x3) ->
   fFORMULA x1;
   fSPEC_LIST x2;
   fID_OPT x3;
   fNODE "rewrite_rl" 3
| CT_right(x1) ->
   fSPEC_LIST x1;
   fNODE "right" 1
| CT_simple_user_tac(x1, x2) ->
   fID x1;
   fTACTIC_ARG_LIST x2;
   fNODE "simple_user_tac" 2
| CT_simplify_eq(x1) ->
   fID_OPT x1;
   fNODE "simplify_eq" 1
| CT_specialize(x1, x2, x3) ->
   fINT_OPT x1;
   fFORMULA x2;
   fSPEC_LIST x3;
   fNODE "specialize" 3
| CT_split(x1) ->
   fSPEC_LIST x1;
   fNODE "split" 1
| CT_superauto(x1, x2, x3, x4) ->
   fINT_OPT x1;
   fID_LIST x2;
   fDESTRUCTING x3;
   fUSINGTDB x4;
   fNODE "superauto" 4
| CT_symmetry -> fNODE "symmetry" 0
| CT_tac_double(x1, x2) ->
   fINT x1;
   fINT x2;
   fNODE "tac_double" 2
| CT_tacsolve(x,l) ->
   fTACTIC_COM x;
   (List.iter fTACTIC_COM l);
   fNODE "tacsolve" (1 + (List.length l))
| CT_tactic_fun(x1, x2) ->
   fID_UNIT_LIST x1;
   fTACTIC_COM x2;
   fNODE "tactic_fun" 2
| CT_then(x,l) ->
   fTACTIC_COM x;
   (List.iter fTACTIC_COM l);
   fNODE "then" (1 + (List.length l))
| CT_transitivity(x1) ->
   fFORMULA x1;
   fNODE "transitivity" 1
| CT_trivial -> fNODE "trivial" 0
| CT_trivial_with(x1) ->
   fID_NE_LIST_OR_STAR x1;
   fNODE "trivial_with" 1
| CT_try(x1) ->
   fTACTIC_COM x1;
   fNODE "try" 1
| CT_use(x1) ->
   fFORMULA x1;
   fNODE "use" 1
| CT_use_inversion(x1, x2, x3) ->
   fID x1;
   fFORMULA x2;
   fID_LIST x3;
   fNODE "use_inversion" 3
| CT_user_tac(x1, x2) ->
   fID x1;
   fTARG_LIST x2;
   fNODE "user_tac" 2
and fTACTIC_OPT = function
| CT_coerce_NONE_to_TACTIC_OPT x -> fNONE x
| CT_coerce_TACTIC_COM_to_TACTIC_OPT x -> fTACTIC_COM x
and fTARG = function
| CT_coerce_BINDING_to_TARG x -> fBINDING x
| CT_coerce_COFIXTAC_to_TARG x -> fCOFIXTAC x
| CT_coerce_FIXTAC_to_TARG x -> fFIXTAC x
| CT_coerce_FORMULA_to_TARG x -> fFORMULA x
| CT_coerce_ID_OR_INT_to_TARG x -> fID_OR_INT x
| CT_coerce_ID_OR_STRING_to_TARG x -> fID_OR_STRING x
| CT_coerce_PATTERN_to_TARG x -> fPATTERN x
| CT_coerce_SIGNED_INT_LIST_to_TARG x -> fSIGNED_INT_LIST x
| CT_coerce_SPEC_LIST_to_TARG x -> fSPEC_LIST x
| CT_coerce_TACTIC_COM_to_TARG x -> fTACTIC_COM x
| CT_coerce_UNFOLD_to_TARG x -> fUNFOLD x
| CT_coerce_UNFOLD_NE_LIST_to_TARG x -> fUNFOLD_NE_LIST x
and fTARG_LIST = function
| CT_targ_list l ->
   (List.iter fTARG l);
   fNODE "targ_list" (List.length l)
and fTEXT = function
| CT_coerce_ID_to_TEXT x -> fID x
| CT_text_formula(x1) ->
   fFORMULA x1;
   fNODE "text_formula" 1
| CT_text_h l ->
   (List.iter fTEXT l);
   fNODE "text_h" (List.length l)
| CT_text_hv l ->
   (List.iter fTEXT l);
   fNODE "text_hv" (List.length l)
| CT_text_op l ->
   (List.iter fTEXT l);
   fNODE "text_op" (List.length l)
| CT_text_path(x1) ->
   fSIGNED_INT_LIST x1;
   fNODE "text_path" 1
| CT_text_v l ->
   (List.iter fTEXT l);
   fNODE "text_v" (List.length l)
and fTHEOREM_GOAL = function
| CT_goal(x1) ->
   fFORMULA x1;
   fNODE "goal" 1
| CT_theorem_goal(x1, x2, x3) ->
   fDEFN_OR_THM x1;
   fID x2;
   fFORMULA x3;
   fNODE "theorem_goal" 3
and fTHM = function
| CT_thm x -> fATOM "thm";
   (f_atom_string x);
   print_string "\n"and fTHM_OPT = function
| CT_coerce_NONE_to_THM_OPT x -> fNONE x
| CT_coerce_THM_to_THM_OPT x -> fTHM x
and fTYPED_FORMULA = function
| CT_typed_formula(x1, x2) ->
   fFORMULA x1;
   fFORMULA x2;
   fNODE "typed_formula" 2
and fUNFOLD = function
| CT_unfold_occ(x1, x2) ->
   fINT_LIST x1;
   fID x2;
   fNODE "unfold_occ" 2
and fUNFOLD_NE_LIST = function
| CT_unfold_ne_list(x,l) ->
   fUNFOLD x;
   (List.iter fUNFOLD l);
   fNODE "unfold_ne_list" (1 + (List.length l))
and fUSING = function
| CT_coerce_NONE_to_USING x -> fNONE x
| CT_using(x1, x2) ->
   fFORMULA x1;
   fSPEC_LIST x2;
   fNODE "using" 2
and fUSINGTDB = function
| CT_coerce_NONE_to_USINGTDB x -> fNONE x
| CT_usingtdb -> fNODE "usingtdb" 0
and fVAR = function
| CT_var x -> fATOM "var";
   (f_atom_string x);
   print_string "\n"and fVARG = function
| CT_coerce_AST_to_VARG x -> fAST x
| CT_coerce_AST_LIST_to_VARG x -> fAST_LIST x
| CT_coerce_BINDER_to_VARG x -> fBINDER x
| CT_coerce_BINDER_LIST_to_VARG x -> fBINDER_LIST x
| CT_coerce_BINDER_NE_LIST_to_VARG x -> fBINDER_NE_LIST x
| CT_coerce_FORMULA_LIST_to_VARG x -> fFORMULA_LIST x
| CT_coerce_FORMULA_OPT_to_VARG x -> fFORMULA_OPT x
| CT_coerce_ID_OPT_OR_ALL_to_VARG x -> fID_OPT_OR_ALL x
| CT_coerce_INT_LIST_to_VARG x -> fINT_LIST x
| CT_coerce_INT_OPT_to_VARG x -> fINT_OPT x
| CT_coerce_STRING_OPT_to_VARG x -> fSTRING_OPT x
| CT_coerce_TACTIC_OPT_to_VARG x -> fTACTIC_OPT x
| CT_coerce_VARG_LIST_to_VARG x -> fVARG_LIST x
and fVARG_LIST = function
| CT_varg_list l ->
   (List.iter fVARG l);
   fNODE "varg_list" (List.length l)
and fVERBOSE_OPT = function
| CT_coerce_NONE_to_VERBOSE_OPT x -> fNONE x
| CT_verbose -> fNODE "verbose" 0
;;
