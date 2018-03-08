(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Globnames
open Constr
open Environ
open Pattern
open Evd
open Proof_type
open Glob_term
open Ltac_pretype

(** These are the entry points for printing terms, context, tac, ... *)


val enable_unfocused_goal_printing: bool ref
val enable_goal_tags_printing      : bool ref
val enable_goal_names_printing     : bool ref

(** Terms *)

val pr_lconstr_env         : env -> evar_map -> constr -> Pp.t
val pr_lconstr             : constr -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]
val pr_lconstr_goal_style_env : env -> evar_map -> constr -> Pp.t

val pr_constr_env          : env -> evar_map -> constr -> Pp.t
val pr_constr              : constr -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]
val pr_constr_goal_style_env : env -> evar_map -> constr -> Pp.t

val pr_constr_n_env        : env -> evar_map -> Notation_term.tolerability -> constr -> Pp.t

(** Same, but resilient to [Nametab] errors. Prints fully-qualified
    names when [shortest_qualid_of_global] has failed. Prints "??"
    in case of remaining issues (such as reference not in env). *)

val safe_pr_lconstr_env         : env -> evar_map -> constr -> Pp.t
val safe_pr_lconstr             : constr -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val safe_pr_constr_env          : env -> evar_map -> constr -> Pp.t
val safe_pr_constr              : constr -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_econstr_env     : env -> evar_map -> EConstr.t -> Pp.t
val pr_econstr         : EConstr.t -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]
val pr_leconstr_env     : env -> evar_map -> EConstr.t -> Pp.t
val pr_leconstr         : EConstr.t -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_econstr_n_env    : env -> evar_map -> Notation_term.tolerability -> EConstr.t -> Pp.t

val pr_etype_env           : env -> evar_map -> EConstr.types -> Pp.t
val pr_letype_env           : env -> evar_map -> EConstr.types -> Pp.t

val pr_open_constr_env     : env -> evar_map -> open_constr -> Pp.t
val pr_open_constr         : open_constr -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_open_lconstr_env    : env -> evar_map -> open_constr -> Pp.t
val pr_open_lconstr        : open_constr -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_constr_under_binders_env  : env -> evar_map -> constr_under_binders -> Pp.t
val pr_constr_under_binders      : constr_under_binders -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_lconstr_under_binders_env : env -> evar_map -> constr_under_binders -> Pp.t
val pr_lconstr_under_binders     : constr_under_binders -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_goal_concl_style_env : env -> evar_map -> EConstr.types -> Pp.t
val pr_ltype_env           : env -> evar_map -> types -> Pp.t
val pr_ltype               : types -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_type_env            : env -> evar_map -> types -> Pp.t
val pr_type                : types -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_closed_glob_n_env   : env -> evar_map -> Notation_term.tolerability -> closed_glob_constr -> Pp.t
val pr_closed_glob_env     : env -> evar_map -> closed_glob_constr -> Pp.t
val pr_closed_glob         : closed_glob_constr -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_ljudge_env          : env -> evar_map -> EConstr.unsafe_judgment -> Pp.t * Pp.t
val pr_ljudge              : EConstr.unsafe_judgment -> Pp.t * Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_lglob_constr_env      : env -> 'a glob_constr_g -> Pp.t
val pr_lglob_constr          : 'a glob_constr_g -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_glob_constr_env       : env -> 'a glob_constr_g -> Pp.t
val pr_glob_constr           : 'a glob_constr_g -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_lconstr_pattern_env : env -> evar_map -> constr_pattern -> Pp.t
val pr_lconstr_pattern     : constr_pattern -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_constr_pattern_env  : env -> evar_map -> constr_pattern -> Pp.t
val pr_constr_pattern      : constr_pattern -> Pp.t
[@@ocaml.deprecated "The global printing API is deprecated, please use the _env functions"]

val pr_cases_pattern       : cases_pattern -> Pp.t

val pr_sort                : evar_map -> Sorts.t -> Pp.t

(** Universe constraints *)

val pr_polymorphic         : bool -> Pp.t
val pr_cumulative          : bool -> bool -> Pp.t
val pr_universe_instance   : evar_map -> Univ.UContext.t -> Pp.t
val pr_universe_ctx        : evar_map -> ?variance:Univ.Variance.t array ->
  Univ.UContext.t -> Pp.t
val pr_universe_ctx_set    : evar_map -> Univ.ContextSet.t -> Pp.t
val pr_constant_universes  : evar_map -> Entries.constant_universes_entry -> Pp.t
val pr_cumulativity_info   : evar_map -> Univ.CumulativityInfo.t -> Pp.t

(** Printing global references using names as short as possible *)

val pr_global_env          : Id.Set.t -> global_reference -> Pp.t
val pr_global              : global_reference -> Pp.t

val pr_constant            : env -> Constant.t -> Pp.t
val pr_existential_key     : evar_map -> Evar.t -> Pp.t
val pr_existential         : env -> evar_map -> existential -> Pp.t
val pr_constructor         : env -> constructor -> Pp.t
val pr_inductive           : env -> inductive -> Pp.t
val pr_evaluable_reference : evaluable_global_reference -> Pp.t

val pr_pconstant           : env -> pconstant -> Pp.t
val pr_pinductive          : env -> pinductive -> Pp.t
val pr_pconstructor        : env -> pconstructor -> Pp.t


(** Contexts *)
(** Display compact contexts of goals (simple hyps on the same line) *)
val set_compact_context : bool -> unit
val get_compact_context : unit -> bool

val pr_context_unlimited   : env -> evar_map -> Pp.t
val pr_ne_context_of       : Pp.t -> env -> evar_map -> Pp.t

val pr_named_decl          : env -> evar_map -> Context.Named.Declaration.t -> Pp.t
val pr_compacted_decl      : env -> evar_map -> Context.Compacted.Declaration.t -> Pp.t
val pr_rel_decl            : env -> evar_map -> Context.Rel.Declaration.t -> Pp.t

val pr_named_context       : env -> evar_map -> Context.Named.t -> Pp.t
val pr_named_context_of    : env -> evar_map -> Pp.t
val pr_rel_context         : env -> evar_map -> Context.Rel.t -> Pp.t
val pr_rel_context_of      : env -> evar_map -> Pp.t
val pr_context_of          : env -> evar_map -> Pp.t

(** Predicates *)

val pr_predicate           : ('a -> Pp.t) -> (bool * 'a list) -> Pp.t
val pr_cpred               : Cpred.t -> Pp.t
val pr_idpred              : Id.Pred.t -> Pp.t
val pr_transparent_state   : transparent_state -> Pp.t

(** Proofs, these functions obey [Hyps Limit] and [Compact contexts]. *)

val pr_goal                : goal sigma -> Pp.t

(** [pr_subgoals ~pr_first pp sigma seeds shelf focus_stack unfocused goals]
   prints the goals of the list [goals] followed by the goals in
   [unfocused], in a short way (typically only the conclusion) except
   for the first goal if [pr_first] is true. This function can be
   replaced by another one by calling [set_printer_pr] (see below),
   typically by plugin writers. The default printer prints only the
   focused goals unless the conrresponding option
   [enable_unfocused_goal_printing] is set. [seeds] is for printing
   dependent evars (mainly for emacs proof tree mode). *)
val pr_subgoals            : ?pr_first:bool -> Pp.t option -> evar_map -> seeds:goal list -> shelf:goal list -> stack:int list -> unfocused:goal list -> goals:goal list -> Pp.t

val pr_subgoal             : int -> evar_map -> goal list -> Pp.t
val pr_concl               : int -> evar_map -> goal -> Pp.t

val pr_open_subgoals       : proof:Proof.t -> Pp.t
val pr_nth_open_subgoal    : proof:Proof.t -> int -> Pp.t
val pr_evar                : evar_map -> (Evar.t * evar_info) -> Pp.t
val pr_evars_int           : evar_map -> shelf:goal list -> givenup:goal list -> int -> evar_info Evar.Map.t -> Pp.t
val pr_evars               : evar_map -> evar_info Evar.Map.t -> Pp.t
val pr_ne_evar_set         : Pp.t -> Pp.t -> evar_map ->
  Evar.Set.t -> Pp.t

val pr_prim_rule           : prim_rule -> Pp.t

(** Backwards compatibility *)

val prterm                 : constr -> Pp.t (** = pr_lconstr *)


(** Declarations for the "Print Assumption" command *)
type axiom =
  | Constant of Constant.t (* An axiom or a constant. *)
  | Positive of MutInd.t (* A mutually inductive definition which has been assumed positive. *)
  | Guarded of Constant.t (* a constant whose (co)fixpoints have been assumed to be guarded *)

type context_object =
  | Variable of Id.t (* A section variable or a Let definition *)
  | Axiom of axiom * (Label.t * Context.Rel.t * types) list
  | Opaque of Constant.t     (* An opaque constant. *)
  | Transparent of Constant.t

module ContextObjectSet : Set.S with type elt = context_object
module ContextObjectMap : CMap.ExtS
  with type key = context_object and module Set := ContextObjectSet

val pr_assumptionset : env -> evar_map -> types ContextObjectMap.t -> Pp.t

val pr_goal_by_id : proof:Proof.t -> Id.t -> Pp.t

type printer_pr = {
 pr_subgoals            : ?pr_first:bool -> Pp.t option -> evar_map -> seeds:goal list -> shelf:goal list -> stack:int list -> unfocused:goal list -> goals:goal list -> Pp.t;

 pr_subgoal             : int -> evar_map -> goal list -> Pp.t;
 pr_goal                : goal sigma -> Pp.t;
}

val set_printer_pr : printer_pr -> unit

val default_printer_pr : printer_pr

