
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Environ
open Reduction
open Proof_trees
open Refiner
open Evar_refiner
open Tacred
(*i*)

(* Operations for handling terms under a local typing context. *)

type 'a sigma

val sig_it  : 'a sigma   -> 'a
val sig_sig : goal sigma -> global_constraints
val project : goal sigma -> evar_declarations

val re_sig : 'a -> global_constraints -> 'a sigma

val unpackage : 'a sigma -> global_constraints ref * 'a
val repackage : global_constraints ref -> 'a -> 'a sigma
val apply_sig_tac :
  global_constraints ref -> ('a sigma -> 'b sigma * 'c) -> 'a -> 'b * 'c

val pf_concl              : goal sigma -> constr
val pf_env                : goal sigma -> unsafe_env
val pf_hyps               : goal sigma -> typed_type signature
val pf_untyped_hyps       : goal sigma -> constr signature
val pf_nth_hyp            : goal sigma -> int -> identifier * constr
val pf_ctxt               : goal sigma -> ctxtty
val pf_global             : goal sigma -> identifier -> constr
val pf_parse_const        : goal sigma -> string -> constr
val pf_type_of            : goal sigma -> constr -> constr
val pf_check_type         : goal sigma -> constr -> constr -> constr
val pf_fexecute           : goal sigma -> constr -> unsafe_judgment
val hnf_type_of           : goal sigma -> constr -> constr

val pf_get_hyp             : goal sigma -> identifier -> constr

val pf_reduction_of_redexp : goal sigma -> red_expr -> constr -> constr

val pf_reduce : 'a reduction_function -> goal sigma -> constr -> constr

val pf_whd_betadeltaiota       : goal sigma -> constr -> constr
val pf_whd_betadeltaiota_stack : goal sigma -> 'a stack_reduction_function
val pf_hnf_constr              : goal sigma -> constr -> constr
val pf_red_product             : goal sigma -> constr -> constr
val pf_nf                      : goal sigma -> constr -> constr
val pf_nf_betaiota             : goal sigma -> constr -> constr
val pf_one_step_reduce         : goal sigma -> constr -> constr
val pf_reduce_to_mind : goal sigma -> constr -> constr * constr * constr
val pf_reduce_to_ind  : goal sigma  -> constr -> section_path * constr * constr
val pf_compute        : goal sigma -> constr -> constr
val pf_unfoldn        : (int list * section_path) list -> goal sigma 
                        -> constr -> constr

val pf_const_value : goal sigma -> constr -> constr
val pf_conv_x      : goal sigma -> constr -> constr -> bool
val pf_conv_x_leq  : goal sigma -> constr -> constr -> bool

type validation            = proof_tree list -> proof_tree
type tactic                = goal sigma -> (goal list sigma * validation)
type transformation_tactic = proof_tree -> (goal list * validation)

val frontier : transformation_tactic


(*s Functions for handling the state of the proof editor. *)

type pftreestate

val proof_of_pftreestate    : pftreestate -> proof_tree
val cursor_of_pftreestate   : pftreestate -> int list
val is_top_pftreestate      : pftreestate -> bool
val evc_of_pftreestate      : pftreestate -> global_constraints
val top_goal_of_pftreestate : pftreestate -> goal sigma
val nth_goal_of_pftreestate : int -> pftreestate -> goal sigma
val traverse                : int -> pftreestate -> pftreestate
val weak_undo_pftreestate   : pftreestate -> pftreestate
val solve_nth_pftreestate   : int -> tactic -> pftreestate -> pftreestate
val solve_pftreestate       : tactic -> pftreestate -> pftreestate
val mk_pftreestate          : goal -> pftreestate
val extract_pftreestate     : pftreestate -> constr
val first_unproven          : pftreestate -> pftreestate
val last_unproven           : pftreestate -> pftreestate
val nth_unproven            : int -> pftreestate -> pftreestate
val node_prev_unproven      : int -> pftreestate -> pftreestate
val node_next_unproven      : int -> pftreestate -> pftreestate
val next_unproven           : pftreestate -> pftreestate
val prev_unproven           : pftreestate -> pftreestate
val top_of_tree             : pftreestate -> pftreestate
val change_constraints_pftreestate :
  global_constraints -> pftreestate -> pftreestate


(*s Tacticals re-exported from the Refiner module. *)

val tclIDTAC         : tactic
val tclORELSE        : tactic -> tactic -> tactic
val tclTHEN          : tactic -> tactic -> tactic
val tclTHEN_i        : tactic -> (int -> tactic) -> int -> tactic
val tclTHENL         : tactic -> tactic -> tactic
val tclTHENS         : tactic -> tactic list -> tactic
val tclTHENSI        : tactic -> tactic list -> tactic
val tclREPEAT        : tactic -> tactic
val tclFIRST         : tactic list -> tactic
val tclSOLVE         : tactic list -> tactic
val tclTRY           : tactic -> tactic
val tclTHENTRY       : tactic -> tactic -> tactic
val tclCOMPLETE      : tactic -> tactic
val tclAT_LEAST_ONCE : tactic -> tactic
val tclFAIL          : tactic
val tclDO            : int -> tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclNOTSAMEGOAL   : tactic -> tactic
val tclINFO          : tactic -> tactic

val unTAC         : tactic -> goal sigma -> proof_tree sigma
val vernac_tactic : tactic_expression -> tactic
val context       : ctxtty -> tactic


(*s The most primitive tactics. *)

val refiner         : rule -> tactic
val introduction    : identifier -> tactic
val intro_replacing : identifier -> tactic
val refine          : constr -> tactic
val convert_concl   : constr -> tactic
val convert_hyp     : identifier -> constr -> tactic
val thin            : identifier list -> tactic
val move_hyp        : bool -> identifier -> identifier -> tactic
val mutual_fix      : identifier list -> int list -> constr list -> tactic
val mutual_cofix    : identifier list -> constr list -> tactic
val rename_bound_var_goal : tactic


(*s Tactics handling a list of goals. *)

type validation_list = proof_tree list -> proof_tree list

type tactic_list = (goal list sigma) -> (goal list sigma) * validation_list

val first_goal         : 'a list sigma -> 'a sigma
val goal_goal_list     : 'a sigma -> 'a list sigma
val apply_tac_list     : tactic -> tactic_list
val then_tactic_list   : tactic_list -> tactic_list -> tactic_list
val tactic_list_tactic : tactic_list -> tactic
val tclFIRSTLIST       : tactic_list list -> tactic_list
val tclIDTAC_list      : tactic_list


(*s Walking constraints re-exported. *)

type walking_constraints = Evar_refiner.walking_constraints

type 'a result_w_tactic  = walking_constraints -> walking_constraints * 'a
type w_tactic            = walking_constraints -> walking_constraints

val startWalk : 
  goal sigma -> walking_constraints * (walking_constraints -> tactic)

val walking_THEN        : 'a result_w_tactic -> ('a -> tactic) -> tactic
val walking             : w_tactic -> tactic
val w_Focusing_THEN     : section_path -> 'a result_w_tactic 
                          -> ('a -> w_tactic) -> w_tactic
val w_Declare           : section_path -> constr -> w_tactic
val w_Declare_At        : section_path -> section_path -> constr -> w_tactic
val w_Define            : section_path -> constr -> w_tactic
val w_Underlying        : walking_constraints -> evar_declarations
val w_env               : walking_constraints -> unsafe_env
val w_hyps              : walking_constraints -> context
val w_type_of           : walking_constraints -> constr -> constr
val w_add_sign          : (identifier * typed_type) 
                          -> walking_constraints -> walking_constraints
val w_IDTAC             : w_tactic
val w_ORELSE            : w_tactic -> w_tactic -> w_tactic
val ctxt_type_of        : readable_constraints -> constr -> constr
val w_whd_betadeltaiota : walking_constraints -> constr -> constr
val w_hnf_constr        : walking_constraints -> constr -> constr
val w_conv_x            : walking_constraints -> constr -> constr -> bool
val w_const_value       : walking_constraints -> constr -> constr
val w_defined_const     : walking_constraints -> constr -> bool


(*s Tactic Registration. *)

val add_tactic         : string -> (tactic_arg list -> tactic) -> unit
val overwriting_tactic : string -> (tactic_arg list -> tactic) -> unit


(*s Hiding the implementation of tactics. *)

val hide_tactic  : 
  string -> (tactic_arg list -> tactic) -> (tactic_arg list -> tactic)

val overwrite_hidden_tactic : 
  string -> (tactic_arg list -> tactic) -> (tactic_arg list -> tactic)


type 'a hide_combinator = string -> ('a -> tactic) -> ('a -> tactic)

val hide_atomic_tactic  : string -> tactic -> tactic
val hide_constr_tactic  : constr hide_combinator
val hide_constrl_tactic : (constr list) hide_combinator
val hide_numarg_tactic  : int hide_combinator
val hide_ident_tactic   : identifier hide_combinator
val hide_identl_tactic  : (identifier list) hide_combinator
val hide_string_tactic  : string hide_combinator
val hide_bindl_tactic   : ((bindOcc * constr) list) hide_combinator
val hide_cbindl_tactic  : (constr * (bindOcc * constr) list) hide_combinator
val hide_cbindll_tactic : 
  ((constr * (bindOcc * constr) list) list) hide_combinator

