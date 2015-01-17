(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Globnames
open Term
open Context
open Environ
open Pattern
open Evd
open Proof_type
open Glob_term

(** These are the entry points for printing terms, context, tac, ... *)

(** Terms *)

val pr_lconstr_env         : env -> evar_map -> constr -> std_ppcmds
val pr_lconstr             : constr -> std_ppcmds
val pr_lconstr_goal_style_env : env -> evar_map -> constr -> std_ppcmds

val pr_constr_env          : env -> evar_map -> constr -> std_ppcmds
val pr_constr              : constr -> std_ppcmds
val pr_constr_goal_style_env : env -> evar_map -> constr -> std_ppcmds

(** Same, but resilient to [Nametab] errors. Prints fully-qualified
    names when [shortest_qualid_of_global] has failed. Prints "??"
    in case of remaining issues (such as reference not in env). *)

val safe_pr_lconstr_env         : env -> evar_map -> constr -> std_ppcmds
val safe_pr_lconstr             : constr -> std_ppcmds

val safe_pr_constr_env          : env -> evar_map -> constr -> std_ppcmds
val safe_pr_constr              : constr -> std_ppcmds


val pr_open_constr_env     : env -> evar_map -> open_constr -> std_ppcmds
val pr_open_constr         : open_constr -> std_ppcmds

val pr_open_lconstr_env    : env -> evar_map -> open_constr -> std_ppcmds
val pr_open_lconstr        : open_constr -> std_ppcmds

val pr_constr_under_binders_env  : env -> evar_map -> constr_under_binders -> std_ppcmds
val pr_constr_under_binders      : constr_under_binders -> std_ppcmds

val pr_lconstr_under_binders_env : env -> evar_map -> constr_under_binders -> std_ppcmds
val pr_lconstr_under_binders     : constr_under_binders -> std_ppcmds

val pr_goal_concl_style_env : env -> evar_map -> types -> std_ppcmds
val pr_ltype_env           : env -> evar_map -> types -> std_ppcmds
val pr_ltype               : types -> std_ppcmds

val pr_type_env            : env -> evar_map -> types -> std_ppcmds
val pr_type                : types -> std_ppcmds

val pr_closed_glob_env     : env -> evar_map -> closed_glob_constr -> std_ppcmds
val pr_closed_glob         : closed_glob_constr -> std_ppcmds

val pr_ljudge_env          : env -> evar_map -> unsafe_judgment -> std_ppcmds * std_ppcmds
val pr_ljudge              : unsafe_judgment -> std_ppcmds * std_ppcmds

val pr_lglob_constr_env      : env -> glob_constr -> std_ppcmds
val pr_lglob_constr          : glob_constr -> std_ppcmds

val pr_glob_constr_env       : env -> glob_constr -> std_ppcmds
val pr_glob_constr           : glob_constr -> std_ppcmds

val pr_lconstr_pattern_env : env -> evar_map -> constr_pattern -> std_ppcmds
val pr_lconstr_pattern     : constr_pattern -> std_ppcmds

val pr_constr_pattern_env  : env -> evar_map -> constr_pattern -> std_ppcmds
val pr_constr_pattern      : constr_pattern -> std_ppcmds

val pr_cases_pattern       : cases_pattern -> std_ppcmds

val pr_sort                : evar_map -> sorts -> std_ppcmds

(** Universe constraints *)

val pr_polymorphic         : bool -> std_ppcmds
val pr_universe_ctx        : Univ.universe_context -> std_ppcmds

(** Printing global references using names as short as possible *)

val pr_global_env          : Id.Set.t -> global_reference -> std_ppcmds
val pr_global              : global_reference -> std_ppcmds

val pr_constant            : env -> constant -> std_ppcmds
val pr_existential_key     : evar_map -> existential_key -> std_ppcmds
val pr_existential         : env -> evar_map -> existential -> std_ppcmds
val pr_constructor         : env -> constructor -> std_ppcmds
val pr_inductive           : env -> inductive -> std_ppcmds
val pr_evaluable_reference : evaluable_global_reference -> std_ppcmds

val pr_pconstant           : env -> pconstant -> std_ppcmds
val pr_pinductive          : env -> pinductive -> std_ppcmds
val pr_pconstructor        : env -> pconstructor -> std_ppcmds


(** Contexts *)

val pr_context_unlimited   : env -> evar_map -> std_ppcmds
val pr_ne_context_of       : std_ppcmds -> env -> evar_map -> std_ppcmds

val pr_var_decl            : env -> evar_map -> named_declaration -> std_ppcmds
val pr_var_list_decl       : env -> evar_map -> named_list_declaration -> std_ppcmds
val pr_rel_decl            : env -> evar_map -> rel_declaration -> std_ppcmds

val pr_named_context       : env -> evar_map -> named_context -> std_ppcmds
val pr_named_context_of    : env -> evar_map -> std_ppcmds
val pr_rel_context         : env -> evar_map -> rel_context -> std_ppcmds
val pr_rel_context_of      : env -> evar_map -> std_ppcmds
val pr_context_of          : env -> evar_map -> std_ppcmds

(** Predicates *)

val pr_predicate           : ('a -> std_ppcmds) -> (bool * 'a list) -> std_ppcmds
val pr_cpred               : Cpred.t -> std_ppcmds
val pr_idpred              : Id.Pred.t -> std_ppcmds
val pr_transparent_state   : transparent_state -> std_ppcmds

(** Proofs *)

val pr_goal                : goal sigma -> std_ppcmds
val pr_subgoals            : ?pr_first:bool -> string option -> evar_map -> evar list -> Goal.goal list -> int list -> goal list -> std_ppcmds
val pr_subgoal             : int -> evar_map -> goal list -> std_ppcmds
val pr_concl               : int -> evar_map -> goal -> std_ppcmds

val pr_open_subgoals       : ?proof:Proof.proof -> unit -> std_ppcmds
val pr_nth_open_subgoal    : int -> std_ppcmds
val pr_evar                : evar_map -> (evar * evar_info) -> std_ppcmds
val pr_evars_int           : evar_map -> int -> evar_info Evar.Map.t -> std_ppcmds
val pr_evars               : evar_map -> evar_info Evar.Map.t -> std_ppcmds

val pr_prim_rule           : prim_rule -> std_ppcmds

(** Emacs/proof general support
   (emacs_str s) outputs
    - s if emacs mode,
    - nothing otherwise.
    This function was previously used to insert special chars like
    [(String.make 1 (Char.chr 253))] to parenthesize sub-parts of the
    proof context for proof by pointing. This part of the code is
    removed for now because it interacted badly with utf8. We may put
    it back some day using some xml-like tags instead of special
    chars. See for example the <prompt> tag in the prompt when in
    emacs mode. *)
val emacs_str              : string -> string

(** Backwards compatibility *)

val prterm                 : constr -> std_ppcmds (** = pr_lconstr *)


(** spiwack: printer function for sets of Environ.assumption.
            It is used primarily by the Print Assumption command. *)
val pr_assumptionset :
  env -> Term.types Assumptions.ContextObjectMap.t ->std_ppcmds

val pr_goal_by_id : string -> std_ppcmds

type printer_pr = {
 pr_subgoals            : ?pr_first:bool -> string option -> evar_map -> evar list -> Goal.goal list -> int list -> goal list -> std_ppcmds;
 pr_subgoal             : int -> evar_map -> goal list -> std_ppcmds;
 pr_goal                : goal sigma -> std_ppcmds;
};;

val set_printer_pr : printer_pr -> unit

val default_printer_pr : printer_pr

