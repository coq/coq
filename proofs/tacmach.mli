(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Environ
open Evd
open Reduction
open Proof_trees
open Proof_type
open Refiner
open Tacred
(*i*)

(* Operations for handling terms under a local typing context. *)

type 'a sigma   = 'a Proof_type.sigma;;
type validation = Proof_type.validation;;
type tactic     = Proof_type.tactic;;

val sig_it  : 'a sigma   -> 'a
val project : goal sigma -> evar_map

val re_sig : 'a -> evar_map -> 'a sigma

val unpackage : 'a sigma -> evar_map ref * 'a
val repackage : evar_map ref -> 'a -> 'a sigma
val apply_sig_tac :
  evar_map ref -> ('a sigma -> 'b sigma * 'c) -> 'a -> 'b * 'c

val pf_concl              : goal sigma -> constr
val pf_env                : goal sigma -> env
val pf_hyps               : goal sigma -> named_context
(*i val pf_untyped_hyps       : goal sigma -> (identifier * constr) list i*)
val pf_hyps_types         : goal sigma -> (identifier * constr) list
val pf_nth_hyp_id         : goal sigma -> int -> identifier
val pf_last_hyp           : goal sigma -> named_declaration
val pf_ids_of_hyps        : goal sigma -> identifier list
val pf_global             : goal sigma -> identifier -> constr
val pf_parse_const        : goal sigma -> string -> constr
val pf_type_of            : goal sigma -> constr -> constr
val pf_check_type         : goal sigma -> constr -> constr -> constr
val pf_execute            : goal sigma -> constr -> unsafe_judgment
val hnf_type_of           : goal sigma -> constr -> constr

val pf_interp_constr      : goal sigma -> Coqast.t -> constr
val pf_interp_type        : goal sigma -> Coqast.t -> constr

val pf_get_hyp            : goal sigma -> identifier -> named_declaration
val pf_get_hyp_typ        : goal sigma -> identifier -> types

val pf_reduction_of_redexp : goal sigma -> red_expr -> constr -> constr



val pf_reduce : 
  (env -> evar_map -> constr -> constr) ->
    goal sigma -> constr -> constr

val pf_whd_betadeltaiota       : goal sigma -> constr -> constr
val pf_whd_betadeltaiota_stack : goal sigma -> constr -> constr * constr list 
val pf_hnf_constr              : goal sigma -> constr -> constr
val pf_red_product             : goal sigma -> constr -> constr
val pf_nf                      : goal sigma -> constr -> constr
val pf_nf_betaiota             : goal sigma -> constr -> constr
val pf_reduce_to_quantified_ind : goal sigma -> types -> inductive * types
val pf_reduce_to_atomic_ind     : goal sigma -> types -> inductive * types
val pf_compute                 : goal sigma -> constr -> constr
val pf_unfoldn    : (int list * Closure.evaluable_global_reference) list
        -> goal sigma -> constr -> constr

val pf_const_value : goal sigma -> constant -> constr
val pf_conv_x      : goal sigma -> constr -> constr -> bool
val pf_conv_x_leq  : goal sigma -> constr -> constr -> bool

type transformation_tactic = proof_tree -> (goal list * validation)

val frontier : transformation_tactic


(*s Functions for handling the state of the proof editor. *)

type pftreestate = Refiner.pftreestate

val proof_of_pftreestate    : pftreestate -> proof_tree
val cursor_of_pftreestate   : pftreestate -> int list
val is_top_pftreestate      : pftreestate -> bool
val evc_of_pftreestate      : pftreestate -> evar_map
val top_goal_of_pftreestate : pftreestate -> goal sigma
val nth_goal_of_pftreestate : int -> pftreestate -> goal sigma
val traverse                : int -> pftreestate -> pftreestate
val weak_undo_pftreestate   : pftreestate -> pftreestate
val solve_nth_pftreestate   : int -> tactic -> pftreestate -> pftreestate
val solve_pftreestate       : tactic -> pftreestate -> pftreestate
val mk_pftreestate          : goal -> pftreestate
val extract_open_pftreestate : pftreestate -> constr * (int * types) list
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
  evar_map -> pftreestate -> pftreestate

(*s Tacticals re-exported from the Refiner module. *)

(* A special exception for levels for the Fail tactic *)
exception FailError of int

val tclIDTAC         : tactic
val tclORELSE        : tactic -> tactic -> tactic
val tclTHEN          : tactic -> tactic -> tactic
val tclTHENLIST      : tactic list -> tactic
val tclTHEN_i        : tactic -> (int -> tactic) -> tactic
val tclTHENL         : tactic -> tactic -> tactic
val tclTHENS         : tactic -> tactic list -> tactic
val tclTHENSi        : tactic -> tactic list -> (int -> tactic) -> tactic
val tclTHENST        : tactic -> tactic list -> tactic -> tactic
val tclTHENSI        : tactic -> tactic list -> tactic
val tclREPEAT        : tactic -> tactic
val tclREPEAT_MAIN   : tactic -> tactic
val tclFIRST         : tactic list -> tactic
val tclSOLVE         : tactic list -> tactic
val tclTRY           : tactic -> tactic
val tclTHENTRY       : tactic -> tactic -> tactic
val tclCOMPLETE      : tactic -> tactic
val tclAT_LEAST_ONCE : tactic -> tactic
val tclFAIL          : int -> tactic
val tclDO            : int -> tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclNOTSAMEGOAL   : tactic -> tactic
val tclINFO          : tactic -> tactic

val unTAC         : tactic -> goal sigma -> proof_tree sigma
val vernac_tactic : tactic_expression -> tactic

(*s The most primitive tactics. *)

val refiner         : rule -> tactic
val introduction    : identifier -> tactic
val intro_replacing : identifier -> tactic
val internal_cut    : identifier -> types -> tactic
val internal_cut_rev : identifier -> types -> tactic
val refine          : constr -> tactic
val convert_concl   : types -> tactic
val convert_hyp     : identifier -> types -> tactic
val convert_deftype : identifier -> types -> tactic
val convert_defbody : identifier -> constr -> tactic
val thin            : identifier list -> tactic
val thin_body       : identifier list -> tactic
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


(*s Tactic Registration. *)

val add_tactic         : string -> (tactic_arg list -> tactic) -> unit
val overwriting_tactic : string -> (tactic_arg list -> tactic) -> unit


(*s Transformation of tactic arguments. *)

type ('a,'b) parse_combinator = ('a -> tactic) -> ('b -> tactic)

val tactic_com       : (constr,Coqast.t) parse_combinator
val tactic_com_sort  : (constr,Coqast.t) parse_combinator
val tactic_com_list  : (constr list, Coqast.t list) parse_combinator

val tactic_bind_list : ((bindOcc * constr) list,
                        (bindOcc * Coqast.t) list) parse_combinator

val tactic_com_bind_list : 
  (constr   * (bindOcc * constr)   list,
   Coqast.t * (bindOcc * Coqast.t) list) parse_combinator

val tactic_com_bind_list_list :  
  ((constr   * (bindOcc * constr)   list) list, 
   (Coqast.t * (bindOcc * Coqast.t) list) list) parse_combinator


(*s Hiding the implementation of tactics. *)

val hide_tactic  : 
  string -> (tactic_arg list -> tactic) -> (tactic_arg list -> tactic)

val overwrite_hidden_tactic : 
  string -> (tactic_arg list -> tactic) -> (tactic_arg list -> tactic)


type 'a hide_combinator = string -> ('a -> tactic) -> ('a -> tactic)

val hide_atomic_tactic  : string -> tactic -> tactic
val hide_constr_tactic  : constr hide_combinator
val hide_openconstr_tactic  : Pretyping.open_constr hide_combinator
val hide_constrl_tactic : (constr list) hide_combinator
val hide_numarg_tactic  : int hide_combinator
val hide_ident_tactic   : identifier hide_combinator
val hide_identl_tactic  : hyp_location list hide_combinator
val hide_string_tactic  : string hide_combinator
val hide_bindl_tactic   : ((bindOcc * constr) list) hide_combinator
val hide_cbindl_tactic  : (constr * (bindOcc * constr) list) hide_combinator
val hide_cbindll_tactic : 
  ((constr * (bindOcc * constr) list) list) hide_combinator


(*s Pretty-printing functions. *)

(*i*)
open Pp
(*i*)

val pr_com    : evar_map -> goal -> Coqast.t -> std_ppcmds
val pr_gls    : goal sigma -> std_ppcmds
val pr_glls   : goal list sigma -> std_ppcmds
val pr_tactic : tactic_expression -> std_ppcmds
