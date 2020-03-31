(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Pattern
open Evd
open Glob_term
open Ltac_pretype
open Notation_term

(** These are the entry points for printing terms, context, tac, ... *)

val print_goal_tag_opt_name : string list

(** Terms *)

(** Printers for terms.

    The "lconstr" variant does not require parentheses to isolate the
    expression from the surrounding context (for instance [3 + 4]
    will be written [3 + 4]). The "constr" variant (w/o "l")
    enforces parentheses whenever the term is not an atom (for
    instance, [3] will be written [3] but [3 + 4] will be
    written [(3 + 4)].

    [~inctx:true] indicates that the term is intended to be printed in
    a context where its type is known so that a head coercion would be
    skipped, or implicit arguments inferable from the context will not
    be made explicit. For instance, if [foo] is declared as a
    coercion, [foo bar] will be printed as [bar] if [inctx] is [true]
    and as [foo bar] otherwise.

    [~scope:some_scope_name] indicates that the head of the term is
    intended to be printed in scope [some_scope_name]. It defaults to
    [None].

    [~impargs:some_list_of_binding_kind] indicates the implicit arguments
    of the external quatification. Only used for printing types (not
    terms), and at toplevel (only "l" versions). It defaults to [None].

    [~lax:true] is for debugging purpose. It defaults to [~lax:false]. *)


val pr_constr_env          : ?lax:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> constr -> Pp.t
val pr_lconstr_env         : ?lax:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> constr -> Pp.t

val pr_constr_n_env        : ?lax:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> Constrexpr.entry_relative_level -> constr -> Pp.t

(** Same, but resilient to [Nametab] errors. Prints fully-qualified
    names when [shortest_qualid_of_global] has failed. Prints "??"
    in case of remaining issues (such as reference not in env). *)

val safe_pr_constr_env  : env -> evar_map -> constr -> Pp.t
val safe_pr_lconstr_env : env -> evar_map -> constr -> Pp.t

val pr_econstr_env      : ?lax:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> EConstr.t -> Pp.t
val pr_leconstr_env     : ?lax:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> EConstr.t -> Pp.t

val pr_econstr_n_env    : ?lax:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> Constrexpr.entry_relative_level -> EConstr.t -> Pp.t

val pr_etype_env        : ?lax:bool -> ?goal_concl_style:bool -> env -> evar_map -> EConstr.types -> Pp.t
val pr_letype_env       : ?lax:bool -> ?goal_concl_style:bool -> env -> evar_map -> ?impargs:Glob_term.binding_kind list -> EConstr.types -> Pp.t

val pr_open_constr_env  : ?lax:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> open_constr -> Pp.t
val pr_open_lconstr_env : ?lax:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> open_constr -> Pp.t

val pr_constr_under_binders_env  : env -> evar_map -> constr_under_binders -> Pp.t

val pr_lconstr_under_binders_env : env -> evar_map -> constr_under_binders -> Pp.t

(** Printers for types. Types are printed in scope "type_scope" and
    under the constraint of being of type a sort.

    The "ltype" variant does not require parentheses to isolate the
    expression from the surrounding context (for instance [nat * bool]
    will be written [nat * bool]). The "type" variant (w/o "l")
    enforces parentheses whenever the term is not an atom (for
    instance, [nat] will be written [nat] but [nat * bool] will be
    written [(nat * bool)].

    [~goal_concl_style:true] tells to print the type the same way as
    command [Show] would print a goal. Concretely, it means that all
    names of goal/section variables and all names of variables
    referred by de Bruijn indices (if any) in the given environment
    and all short names of global definitions of the current module
    must be avoided while printing bound variables. Otherwise, short
    names of global definitions are printed qualified and only names
    of goal/section variables and rel names that do _not_ occur in the
    scope of the binder to be printed are avoided.

    [~lax:true] is for debugging purpose. *)

val pr_ltype_env           : ?lax:bool -> ?goal_concl_style:bool -> env -> evar_map -> ?impargs:Glob_term.binding_kind list -> types -> Pp.t
val pr_type_env            : ?lax:bool -> ?goal_concl_style:bool -> env -> evar_map -> types -> Pp.t

val pr_closed_glob_n_env   : ?lax:bool -> ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> Constrexpr.entry_relative_level -> closed_glob_constr -> Pp.t
val pr_closed_glob_env     : ?lax:bool -> ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> closed_glob_constr -> Pp.t

val pr_ljudge_env          : env -> evar_map -> EConstr.unsafe_judgment -> Pp.t * Pp.t

val pr_lglob_constr_env      : env -> 'a glob_constr_g -> Pp.t

val pr_glob_constr_env       : env -> 'a glob_constr_g -> Pp.t

val pr_lconstr_pattern_env : env -> evar_map -> constr_pattern -> Pp.t

val pr_constr_pattern_env  : env -> evar_map -> constr_pattern -> Pp.t

val pr_cases_pattern       : cases_pattern -> Pp.t

val pr_sort                : evar_map -> Sorts.t -> Pp.t

(** Universe constraints *)

val pr_universe_instance   : evar_map -> Univ.Instance.t -> Pp.t
val pr_universe_instance_constraints : evar_map -> Univ.Instance.t -> Univ.Constraint.t -> Pp.t
val pr_universe_ctx        : evar_map -> ?variance:Univ.Variance.t array ->
  Univ.UContext.t -> Pp.t
val pr_abstract_universe_ctx : evar_map -> ?variance:Univ.Variance.t array ->
  ?priv:Univ.ContextSet.t -> Univ.AUContext.t -> Pp.t
val pr_universe_ctx_set    : evar_map -> Univ.ContextSet.t -> Pp.t
val pr_universes  : evar_map ->
  ?variance:Univ.Variance.t array -> ?priv:Univ.ContextSet.t ->
  Declarations.universes -> Pp.t

(** [universe_binders_with_opt_names ref l]

    If [l] is [Some univs] return the universe binders naming the
   bound levels of [ref] by [univs] (generating names for Anonymous).
   May error if the lengths mismatch.

    Otherwise return the bound universe names registered for [ref].

    Inefficient on large contexts due to name generation. *)
val universe_binders_with_opt_names : Univ.AUContext.t ->
  UnivNames.univ_name_list option -> UnivNames.universe_binders

(** Printing global references using names as short as possible *)

val pr_global_env          : Id.Set.t -> GlobRef.t -> Pp.t
val pr_global              : GlobRef.t -> Pp.t

val pr_constant            : env -> Constant.t -> Pp.t
val pr_existential_key     : evar_map -> Evar.t -> Pp.t
val pr_existential         : env -> evar_map -> existential -> Pp.t
val pr_constructor         : env -> constructor -> Pp.t
val pr_inductive           : env -> inductive -> Pp.t
val pr_evaluable_reference : evaluable_global_reference -> Pp.t

val pr_pconstant : env -> evar_map -> pconstant -> Pp.t
val pr_pinductive : env -> evar_map -> pinductive -> Pp.t
val pr_pconstructor : env -> evar_map -> pconstructor -> Pp.t


(** Contexts *)

(** Display compact contexts of goals (simple hyps on the same line) *)
val set_compact_context : bool -> unit
val get_compact_context : unit -> bool

val pr_context_unlimited   : env -> evar_map -> Pp.t
val pr_ne_context_of       : Pp.t -> env -> evar_map -> Pp.t

val pr_named_decl          : env -> evar_map -> Constr.named_declaration -> Pp.t
val pr_compacted_decl      : env -> evar_map -> Constr.compacted_declaration -> Pp.t
val pr_rel_decl            : env -> evar_map -> Constr.rel_declaration -> Pp.t

val pr_named_context       : env -> evar_map -> Constr.named_context -> Pp.t
val pr_named_context_of    : env -> evar_map -> Pp.t
val pr_rel_context         : env -> evar_map -> Constr.rel_context -> Pp.t
val pr_rel_context_of      : env -> evar_map -> Pp.t
val pr_context_of          : env -> evar_map -> Pp.t

(** Predicates *)

val pr_predicate           : ('a -> Pp.t) -> (bool * 'a list) -> Pp.t
val pr_cpred               : Cpred.t -> Pp.t
val pr_idpred              : Id.Pred.t -> Pp.t
val pr_transparent_state   : TransparentState.t -> Pp.t

(** Proofs, these functions obey [Hyps Limit] and [Compact contexts]. *)

(** [pr_goal ~diffs ~og_s g_s] prints the goal specified by [g_s].  If [diffs] is true,
    highlight the differences between the old goal, [og_s], and [g_s].  [g_s] and [og_s] are
    records containing the goal and sigma for, respectively, the new and old proof steps,
    e.g. [{ it = g ; sigma = sigma }].
*)
val pr_goal                : ?diffs:bool -> ?og_s:(Goal.goal sigma) -> Goal.goal sigma -> Pp.t

(** [pr_subgoals ~pr_first ~diffs ~os_map close_cmd sigma ~seeds ~shelf ~stack ~unfocused ~goals]
   prints the goals in [goals] followed by the goals in [unfocused] in a compact form
   (typically only the conclusion).  If [pr_first] is true, print the first goal in full.
   [close_cmd] is printed afterwards verbatim.

   If [diffs] is true, then highlight diffs relative to [os_map] in the output for first goal.
   [os_map] contains sigma for the old proof step and the goal map created by
   [Proof_diffs.make_goal_map].

   This function prints only the focused goals unless the corresponding option [enable_unfocused_goal_printing] is set.
   [seeds] is for printing dependent evars (mainly for emacs proof tree mode).  [shelf] is from
   Proof.proof and is used to identify shelved goals in a message if there are no more subgoals but
   there are non-instantiated existential variables.  [stack] is used to print summary info on unfocused
   goals.
*)
val pr_subgoals            : ?pr_first:bool -> ?diffs:bool -> ?os_map:(evar_map * Goal.goal Evar.Map.t) -> Pp.t option -> evar_map
                             -> seeds:Goal.goal list -> shelf:Goal.goal list -> stack:int list
                             -> unfocused:Goal.goal list -> goals:Goal.goal list -> Pp.t

val pr_subgoal             : int -> evar_map -> Goal.goal list -> Pp.t

(** [pr_concl n ~diffs ~og_s sigma g] prints the conclusion of the goal [g] using [sigma].  The output
    is labelled "subgoal [n]".  If [diffs] is true, highlight the differences between the old conclusion,
    [og_s], and [g]+[sigma].  [og_s] is a record containing the old goal and sigma, e.g. [{ it = g ; sigma = sigma }].
*)
val pr_concl               : int -> ?diffs:bool -> ?og_s:(Goal.goal sigma) -> evar_map -> Goal.goal -> Pp.t

(** [pr_open_subgoals_diff ~quiet ~diffs ~oproof proof] shows the context for [proof] as used by, for example, coqtop.
    The first active goal is printed with all its antecedents and the conclusion.  The other active goals only show their
     conclusions.  If [diffs] is true, highlight the differences between the old proof, [oproof], and [proof].  [quiet]
     disables printing messages as Feedback.
*)
val pr_open_subgoals_diff  : ?quiet:bool -> ?diffs:bool -> ?oproof:Proof.t -> Proof.t -> Pp.t
val pr_open_subgoals       : proof:Proof.t -> Pp.t
val pr_nth_open_subgoal    : proof:Proof.t -> int -> Pp.t
val pr_evar                : evar_map -> (Evar.t * evar_info) -> Pp.t
val pr_evars_int           : evar_map -> shelf:Goal.goal list -> given_up:Goal.goal list -> int -> evar_info Evar.Map.t -> Pp.t
val pr_evars               : evar_map -> evar_info Evar.Map.t -> Pp.t
val pr_ne_evar_set         : Pp.t -> Pp.t -> evar_map ->
  Evar.Set.t -> Pp.t

val print_and_diff : Proof.t option -> Proof.t option -> unit
val print_dependent_evars : Evar.t option -> evar_map -> Evar.t list -> Pp.t

(** Declarations for the "Print Assumption" command *)
type axiom =
  | Constant of Constant.t (* An axiom or a constant. *)
  | Positive of MutInd.t (* A mutually inductive definition which has been assumed positive. *)
  | Guarded of GlobRef.t (* a constant whose (co)fixpoints have been assumed to be guarded *)
  | TypeInType of GlobRef.t (* a constant which relies on type in type *)

type context_object =
  | Variable of Id.t (* A section variable or a Let definition *)
  | Axiom of axiom * (Label.t * Constr.rel_context * types) list
  | Opaque of Constant.t     (* An opaque constant. *)
  | Transparent of Constant.t

module ContextObjectSet : Set.S with type elt = context_object
module ContextObjectMap : CMap.ExtS
  with type key = context_object and module Set := ContextObjectSet

val pr_assumptionset : env -> evar_map -> types ContextObjectMap.t -> Pp.t

val pr_goal_by_id : proof:Proof.t -> Id.t -> Pp.t
val pr_goal_emacs : proof:Proof.t option -> int -> int -> Pp.t

val pr_typing_flags : Declarations.typing_flags -> Pp.t
