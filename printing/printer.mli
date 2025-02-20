(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
*)


val pr_constr_env          : ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> constr -> Pp.t
val pr_lconstr_env         : ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> constr -> Pp.t

val pr_constr_n_env        : ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> Constrexpr.entry_relative_level -> constr -> Pp.t

(** Same, but resilient to [Nametab] errors. Prints fully-qualified
    names when [shortest_qualid_of_global] has failed. Prints "??"
    in case of remaining issues (such as reference not in env). *)

val safe_pr_constr_env  : env -> evar_map -> constr -> Pp.t
val safe_pr_lconstr_env : env -> evar_map -> constr -> Pp.t
val safe_extern_wrapper : (env -> evar_map -> 'a -> 'b) -> env -> evar_map -> 'a -> 'b option

val pr_econstr_env      : ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> EConstr.t -> Pp.t
val pr_leconstr_env     : ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> EConstr.t -> Pp.t

val pr_econstr_n_env    : ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> Constrexpr.entry_relative_level -> EConstr.t -> Pp.t

val pr_etype_env        : ?goal_concl_style:bool -> env -> evar_map -> EConstr.types -> Pp.t
val pr_letype_env       : ?goal_concl_style:bool -> env -> evar_map -> ?impargs:Glob_term.binding_kind list -> EConstr.types -> Pp.t

val pr_open_constr_env  : ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> open_constr -> Pp.t
val pr_open_lconstr_env : ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> open_constr -> Pp.t

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
*)

val pr_ltype_env           : ?goal_concl_style:bool -> env -> evar_map -> ?impargs:Glob_term.binding_kind list -> types -> Pp.t
val pr_type_env            : ?goal_concl_style:bool -> env -> evar_map -> types -> Pp.t

val pr_closed_glob_n_env   : ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> Constrexpr.entry_relative_level -> closed_glob_constr -> Pp.t
val pr_closed_glob_env     : ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name -> env -> evar_map -> closed_glob_constr -> Pp.t

val pr_ljudge_env          : env -> evar_map -> EConstr.unsafe_judgment -> Pp.t * Pp.t

val pr_lglob_constr_env    : env -> evar_map -> 'a glob_constr_g -> Pp.t

val pr_glob_constr_env     : env -> evar_map -> 'a glob_constr_g -> Pp.t

val pr_lconstr_pattern_env : env -> evar_map -> _ constr_pattern_r -> Pp.t

val pr_constr_pattern_env  : env -> evar_map -> _ constr_pattern_r -> Pp.t

val pr_cases_pattern       : cases_pattern -> Pp.t

val pr_sort                : evar_map -> Sorts.t -> Pp.t

(** Universe constraints *)

val pr_universe_instance   : evar_map -> UVars.Instance.t -> Pp.t
val pr_universe_instance_binder : evar_map -> UVars.Instance.t -> Univ.Constraints.t -> Pp.t
val pr_universe_ctx        : evar_map -> ?variance:UVars.Variance.t array ->
  UVars.UContext.t -> Pp.t
val pr_abstract_universe_ctx : evar_map -> ?variance:UVars.Variance.t array ->
  ?priv:Univ.ContextSet.t -> UVars.AbstractContext.t -> Pp.t
val pr_universe_ctx_set    : evar_map -> Univ.ContextSet.t -> Pp.t
val pr_universes  : evar_map ->
  ?variance:UVars.Variance.t array -> ?priv:Univ.ContextSet.t ->
  Declarations.universes -> Pp.t

(** [universe_binders_with_opt_names ref l]

    If [l] is [Some univs] return the universe binders naming the
   bound levels of [ref] by [univs] (generating names for Anonymous).
   May error if the lengths mismatch.

    Otherwise return the bound universe names registered for [ref].

    Inefficient on large contexts due to name generation. *)
val universe_binders_with_opt_names : UVars.AbstractContext.t ->
  (GlobRef.t * UnivNames.full_name_list) option -> UnivNames.universe_binders * UnivNames.rev_binders

(** Printing global references using names as short as possible *)

val pr_global_env          : Id.Set.t -> GlobRef.t -> Pp.t
val pr_global              : GlobRef.t -> Pp.t

val pr_constant            : env -> Constant.t -> Pp.t
val pr_existential_key     : env -> evar_map -> Evar.t -> Pp.t
val pr_existential         : env -> evar_map -> existential -> Pp.t
val pr_constructor         : env -> constructor -> Pp.t
val pr_inductive           : env -> inductive -> Pp.t
val pr_evaluable_reference : Evaluable.t -> Pp.t

val pr_pconstant : env -> evar_map -> pconstant -> Pp.t
val pr_pinductive : env -> evar_map -> pinductive -> Pp.t
val pr_pconstructor : env -> evar_map -> pconstructor -> Pp.t

val pr_notation_interpretation_env : env -> evar_map -> glob_constr -> Pp.t
val pr_notation_interpretation : glob_constr -> Pp.t

(** Contexts *)

(** Display compact contexts of goals (simple hyps on the same line) *)
val set_compact_context : bool -> unit
val get_compact_context : unit -> bool

val pr_context_unlimited   : env -> evar_map -> Pp.t
val pr_ne_context_of       : Pp.t -> env -> evar_map -> Pp.t

val pr_named_decl          : env -> evar_map -> Constr.named_declaration -> Pp.t
val pr_compacted_decl      : env -> evar_map -> Constr.compacted_declaration -> Pp.t
val pr_rel_decl            : env -> evar_map -> Constr.rel_declaration -> Pp.t

val pr_enamed_decl          : env -> evar_map -> EConstr.named_declaration -> Pp.t
val pr_ecompacted_decl      : env -> evar_map -> EConstr.compacted_declaration -> Pp.t
val pr_erel_decl            : env -> evar_map -> EConstr.rel_declaration -> Pp.t

val pr_named_context       : env -> evar_map -> Constr.named_context -> Pp.t
val pr_named_context_of    : env -> evar_map -> Pp.t
val pr_rel_context         : env -> evar_map -> Constr.rel_context -> Pp.t
val pr_rel_context_of      : env -> evar_map -> Pp.t
val pr_context_of          : env -> evar_map -> Pp.t

(** Predicates *)

val pr_predicate           : ('a -> Pp.t) -> (bool * 'a list) -> Pp.t
val pr_cpred               : Cpred.t -> Pp.t
val pr_idpred              : Id.Pred.t -> Pp.t
val pr_prpred              : PRpred.t -> Pp.t
val pr_transparent_state   : TransparentState.t -> Pp.t

(** Proofs, these functions obey [Hyps Limit] and [Compact contexts]. *)

(** [pr_open_subgoals ~quiet ?diffs proof] shows the context for [proof] as used by, for example, coqtop.
    The first active goal is printed with all its antecedents and the conclusion.  The other active goals only show their
     conclusions.  If [diffs] is [Some oproof], highlight the differences between the old proof [oproof], and [proof].  [quiet]
     disables printing messages as Feedback.
*)
val pr_open_subgoals       : ?quiet:bool -> ?diffs:Proof.t option -> Proof.t -> Pp.t
val pr_nth_open_subgoal    : proof:Proof.t -> int -> Pp.t
val pr_evar                : evar_map -> (Evar.t * undefined evar_info) -> Pp.t
val pr_evars_int           : evar_map -> shelf:Evar.t list -> given_up:Evar.t list -> int -> undefined evar_info Evar.Map.t -> Pp.t
val pr_ne_evar_set         : Pp.t -> Pp.t -> evar_map ->
  Evar.Set.t -> Pp.t

(** Declarations for the "Print Assumption" command *)
type axiom =
  | Constant of Constant.t (* An axiom or a constant. *)
  | Positive of MutInd.t (* A mutually inductive definition which has been assumed positive. *)
  | Guarded of GlobRef.t (* a constant whose (co)fixpoints have been assumed to be guarded *)
  | TypeInType of GlobRef.t (* a constant which relies on type in type *)
  | UIP of MutInd.t (* An inductive using the special reduction rule. *)

type context_object =
  | Variable of Id.t (* A section variable or a Let definition *)
  | Axiom of axiom * (Label.t * Constr.rel_context * types) list
  | Opaque of Constant.t     (* An opaque constant. *)
  | Transparent of Constant.t

module ContextObjectSet : CSet.ExtS with type elt = context_object
module ContextObjectMap : CMap.ExtS
  with type key = context_object and module Set := ContextObjectSet

val pr_assumptionset : env -> evar_map -> types ContextObjectMap.t -> Pp.t

val pr_goal_by_id : proof:Proof.t -> Id.t -> Pp.t
val pr_goal_emacs : proof:Proof.t option -> int -> int -> Pp.t

val pr_typing_flags : Declarations.typing_flags -> Pp.t

(** Tells if flag "Printing Goal Names" is activated *)
val print_goal_names : unit -> bool

module Debug :
sig

val pr_goal : Proofview.Goal.t -> Pp.t

end
(** Debug printers *)
