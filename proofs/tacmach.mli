(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Sign
open Environ
open Evd
open Reduction
open Proof_type
open Refiner
open Redexpr
open Tacexpr
open Rawterm
open Pattern

(** Operations for handling terms under a local typing context. *)

type 'a sigma   = 'a Evd.sigma;;
type tactic     = Proof_type.tactic;;

val sig_it  : 'a sigma   -> 'a
val project : goal sigma -> evar_map

val re_sig : 'a -> evar_map -> 'a sigma

val unpackage : 'a sigma -> evar_map ref * 'a
val repackage : evar_map ref -> 'a -> 'a sigma
val apply_sig_tac :
  evar_map ref -> (goal sigma -> (goal list) sigma) -> goal -> (goal list) 

val pf_concl              : goal sigma -> types
val pf_env                : goal sigma -> env
val pf_hyps               : goal sigma -> named_context
(*i val pf_untyped_hyps       : goal sigma -> (identifier * constr) list i*)
val pf_hyps_types         : goal sigma -> (identifier * types) list
val pf_nth_hyp_id         : goal sigma -> int -> identifier
val pf_last_hyp           : goal sigma -> named_declaration
val pf_ids_of_hyps        : goal sigma -> identifier list
val pf_global             : goal sigma -> identifier -> constr
val pf_parse_const        : goal sigma -> string -> constr
val pf_type_of            : goal sigma -> constr -> types
val pf_check_type         : goal sigma -> constr -> types -> unit
val pf_hnf_type_of        : goal sigma -> constr -> types

val pf_interp_constr      : goal sigma -> Topconstr.constr_expr -> constr
val pf_interp_type        : goal sigma -> Topconstr.constr_expr -> types

val pf_get_hyp            : goal sigma -> identifier -> named_declaration
val pf_get_hyp_typ        : goal sigma -> identifier -> types

val pf_get_new_id  : identifier      -> goal sigma -> identifier
val pf_get_new_ids : identifier list -> goal sigma -> identifier list

val pf_reduction_of_red_expr : goal sigma -> red_expr -> constr -> constr


val pf_apply : (env -> evar_map -> 'a) -> goal sigma -> 'a
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
val pf_unfoldn    : (Termops.occurrences * evaluable_global_reference) list
        -> goal sigma -> constr -> constr

val pf_const_value : goal sigma -> constant -> constr
val pf_conv_x      : goal sigma -> constr -> constr -> bool
val pf_conv_x_leq  : goal sigma -> constr -> constr -> bool

val pf_matches     : goal sigma -> constr_pattern -> constr -> patvar_map
val pf_is_matching : goal sigma -> constr_pattern -> constr -> bool


(** {6 The most primitive tactics. } *)

val refiner                   : rule -> tactic
val introduction_no_check     : identifier -> tactic
val internal_cut_no_check     : bool -> identifier -> types -> tactic
val internal_cut_rev_no_check : bool -> identifier -> types -> tactic
val refine_no_check           : constr -> tactic
val convert_concl_no_check    : types -> cast_kind -> tactic
val convert_hyp_no_check      : named_declaration -> tactic
val thin_no_check             : identifier list -> tactic
val thin_body_no_check        : identifier list -> tactic
val move_hyp_no_check         :
  bool -> identifier -> identifier move_location -> tactic
val rename_hyp_no_check       : (identifier*identifier) list -> tactic
val order_hyps : identifier list -> tactic
val mutual_fix      :
  identifier -> int -> (identifier * int * constr) list -> int -> tactic
val mutual_cofix    : identifier -> (identifier * constr) list -> int -> tactic

(** {6 The most primitive tactics with consistency and type checking } *)

val introduction     : identifier -> tactic
val internal_cut     : bool -> identifier -> types -> tactic
val internal_cut_rev : bool -> identifier -> types -> tactic
val refine           : constr -> tactic
val convert_concl    : types -> cast_kind -> tactic
val convert_hyp      : named_declaration -> tactic
val thin             : identifier list -> tactic
val thin_body        : identifier list -> tactic
val move_hyp         : bool -> identifier -> identifier move_location -> tactic
val rename_hyp       : (identifier*identifier) list -> tactic

(** {6 Tactics handling a list of goals. } *)

type validation_list = proof_tree list -> proof_tree list

type tactic_list = Refiner.tactic_list

val first_goal         : 'a list sigma -> 'a sigma
val goal_goal_list     : 'a sigma -> 'a list sigma
val apply_tac_list     : tactic -> tactic_list
val then_tactic_list   : tactic_list -> tactic_list -> tactic_list
val tactic_list_tactic : tactic_list -> tactic
val tclFIRSTLIST       : tactic_list list -> tactic_list
val tclIDTAC_list      : tactic_list

(** {6 Pretty-printing functions (debug only). } *)
val pr_gls    : goal sigma -> Pp.std_ppcmds
val pr_glls   : goal list sigma -> Pp.std_ppcmds
