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

val pr_in_comment : Pp.t -> Pp.t

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


val pr_constr_env : ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> constr -> Pp.t
val pr_lconstr_env : ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> constr -> Pp.t

val pr_constr_n_env        : ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> Constrexpr.entry_relative_level -> constr -> Pp.t

(** Same, but resilient to [Nametab] errors. Prints fully-qualified
    names when [shortest_qualid_of_global] has failed. Prints "??"
    in case of remaining issues (such as reference not in env). *)

val safe_pr_constr_env  : ?flags:PrintingFlags.t -> env -> evar_map -> constr -> Pp.t
val safe_pr_lconstr_env : ?flags:PrintingFlags.t -> env -> evar_map -> constr -> Pp.t
val safe_extern_wrapper : (env -> evar_map -> 'a -> 'b) -> env -> evar_map -> 'a -> 'b option

val pr_econstr_env : ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> EConstr.t -> Pp.t
val pr_leconstr_env : ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> EConstr.t -> Pp.t

val pr_econstr_n_env : ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> Constrexpr.entry_relative_level -> EConstr.t -> Pp.t

val pr_etype_env : ?goal_concl_style:bool -> ?flags:PrintingFlags.t ->
  env -> evar_map -> EConstr.types -> Pp.t
val pr_letype_env : ?goal_concl_style:bool -> ?flags:PrintingFlags.t ->
  env -> evar_map -> ?impargs:Glob_term.binding_kind list -> EConstr.types -> Pp.t

val pr_constr_under_binders_env : ?flags:PrintingFlags.t -> env -> evar_map -> constr_under_binders -> Pp.t

val pr_lconstr_under_binders_env : ?flags:PrintingFlags.t -> env -> evar_map -> constr_under_binders -> Pp.t

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

val pr_ltype_env : ?goal_concl_style:bool -> ?flags:PrintingFlags.t ->
  env -> evar_map -> ?impargs:Glob_term.binding_kind list -> types -> Pp.t
val pr_type_env : ?goal_concl_style:bool -> ?flags:PrintingFlags.t ->
  env -> evar_map -> types -> Pp.t

val pr_closed_glob_n_env : ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> Constrexpr.entry_relative_level -> closed_glob_constr -> Pp.t
val pr_closed_glob_env : ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> closed_glob_constr -> Pp.t
val pr_closed_lglob_env : ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name -> ?flags:PrintingFlags.t ->
  env -> evar_map -> closed_glob_constr -> Pp.t

val pr_ljudge_env : ?flags:PrintingFlags.t ->
  env -> evar_map -> EConstr.unsafe_judgment -> Pp.t * Pp.t

val pr_lglob_constr_env : ?flags:PrintingFlags.Extern.t ->
  env -> evar_map -> 'a glob_constr_g -> Pp.t

val pr_glob_constr_env : ?flags:PrintingFlags.Extern.t ->
  env -> evar_map -> 'a glob_constr_g -> Pp.t

val pr_lconstr_pattern_env : ?flags:PrintingFlags.Extern.t ->
  env -> evar_map -> constr_pattern -> Pp.t

val pr_constr_pattern_env : ?flags:PrintingFlags.Extern.t ->
  env -> evar_map -> constr_pattern -> Pp.t

val pr_uninstantiated_lconstr_pattern_env : ?flags:PrintingFlags.Extern.t ->
  env -> evar_map -> uninstantiated_pattern -> Pp.t

val pr_uninstantiated_constr_pattern_env : ?flags:PrintingFlags.Extern.t ->
  env -> evar_map -> uninstantiated_pattern -> Pp.t

val pr_cases_pattern : ?flags:PrintingFlags.Extern.t -> cases_pattern -> Pp.t

val pr_sort : ?universes:bool -> ?sorts:bool -> ?qualities:bool -> evar_map -> Sorts.t -> Pp.t

(** Universe constraints *)

val pr_universe_instance   : evar_map -> UVars.Instance.t -> Pp.t
val pr_abstract_universe_binder : evar_map -> UVars.AbstractContext.t -> Pp.t
val pr_universe_ctx        : evar_map -> ?variance:UVars.Variance.t array ->
  UVars.UContext.t -> Pp.t
val pr_abstract_universe_ctx : evar_map -> ?variance:UVars.Variance.t array ->
  ?priv:Univ.ContextSet.t -> UVars.AbstractContext.t -> Pp.t
val pr_sort_context_set : evar_map -> UnivGen.sort_context_set -> Pp.t
val pr_universes  : evar_map ->
  ?variance:UVars.Variance.t array -> ?priv:Univ.ContextSet.t ->
  Declarations.universes -> Pp.t

(** [fill_names ref l]

    Generates names for Anonymous entries in [ref].
    If [l] is [Some univs], use first the names in [univs],
    then those in [ref] and finally generated names.
    Can raise [UniverseLengthMismatch].
    Inefficient on large contexts due to name generation. *)
val fill_names : ?user_names:(GlobRef.t * UnivNames.univ_name_list) ->
  UVars.AbstractContext.t -> UVars.AbstractContext.t

(** Printing global references using names as short as possible *)

val pr_global_env          : Id.Set.t -> GlobRef.t -> Pp.t
val pr_global              : GlobRef.t -> Pp.t

val pr_constant            : env -> Constant.t -> Pp.t
val pr_existential_key     : env -> evar_map -> Evar.t -> Pp.t
val pr_existential : ?flags:PrintingFlags.t -> env -> evar_map -> existential -> Pp.t
val pr_constructor         : env -> constructor -> Pp.t
val pr_inductive           : env -> inductive -> Pp.t
val pr_evaluable_reference : env -> Evaluable.t -> Pp.t

val pr_pconstant : env -> evar_map -> pconstant -> Pp.t
val pr_pinductive : env -> evar_map -> pinductive -> Pp.t
val pr_pconstructor : env -> evar_map -> pconstructor -> Pp.t

val pr_notation_interpretation_env : env -> evar_map -> glob_constr -> Pp.t

(** Contexts *)

val pr_context_unlimited : ?flags:PrintingFlags.t -> env -> evar_map -> Pp.t
val pr_ne_context_of : Pp.t -> ?flags:PrintingFlags.t -> env -> evar_map -> Pp.t

val pr_named_decl : ?flags:PrintingFlags.t ->
  env -> evar_map -> var_status option -> Constr.named_declaration -> Pp.t
val pr_rel_decl : ?flags:PrintingFlags.t ->
  env -> evar_map -> Constr.rel_declaration -> Pp.t

val pr_enamed_decl : ?flags:PrintingFlags.t ->
  env -> evar_map -> var_status option -> EConstr.named_declaration -> Pp.t
val pr_ecompacted_decl : ?flags:PrintingFlags.t ->
  env -> evar_map -> Ppconstr.CompactedDecl.t -> Pp.t
val pr_erel_decl : ?flags:PrintingFlags.t ->
  env -> evar_map -> EConstr.rel_declaration -> Pp.t

val pr_named_context : ?flags:PrintingFlags.t ->
  env -> evar_map -> Constr.named_context -> Pp.t
val pr_named_context_of : ?flags:PrintingFlags.t ->
  env -> evar_map -> Pp.t
val pr_rel_context : ?flags:PrintingFlags.t ->
  env -> evar_map -> Constr.rel_context -> Pp.t
val pr_rel_context_of : ?flags:PrintingFlags.t ->
  env -> evar_map -> Pp.t
val pr_context_of : ?flags:PrintingFlags.t ->
  env -> evar_map -> Pp.t

(** Predicates *)

val pr_predicate           : ('a -> Pp.t) -> (bool * 'a list) -> Pp.t
val pr_cpred               : Cpred.t -> Pp.t
val pr_idpred              : Id.Pred.t -> Pp.t
val pr_prpred              : PRpred.t -> Pp.t
val pr_transparent_state   : TransparentState.t -> Pp.t

val pr_evar : ?flags:PrintingFlags.t ->
  evar_map -> (Evar.t * undefined evar_info) -> Pp.t
val pr_evars_int : ?flags:PrintingFlags.t ->
  evar_map -> shelf:Evar.t list -> given_up:Evar.t list -> int -> undefined evar_info Evar.Map.t -> Pp.t
val pr_ne_evar_set : ?flags:PrintingFlags.t ->
  Pp.t -> Pp.t -> evar_map ->
  Evar.Set.t -> Pp.t

(** Declarations for the "Print Assumption" command *)

val print_all_assumptions : unit -> bool

type axiom =
  | Constant of Constant.t (* An axiom or a constant. *)
  | Positive of MutInd.t (* A mutually inductive definition which has been assumed positive. *)
  | Guarded of GlobRef.t (* a constant whose (co)fixpoints have been assumed to be guarded *)
  | TypeInType of GlobRef.t (* a constant which relies on type in type *)
  | UIP of MutInd.t (* An inductive using the special reduction rule. *)
  | IndicesNotMattering of MutInd.t (* An inductive relying on indices not mattering. *)

type context_object =
  | Variable of Id.t (* A section variable or a Let definition *)
  | Axiom of axiom * (GlobRef.t * Constr.rel_context * types) list
  | Opaque of Constant.t     (* An opaque constant. *)
  | Transparent of Constant.t

module ContextObjectSet : CSet.ExtS with type elt = context_object
module ContextObjectMap : CMap.ExtS
  with type key = context_object and module Set := ContextObjectSet

type theory_assumptions = {
  has_impredicative_set : bool;
  has_rewrite_rules : bool;
  has_type_in_type : bool;
}

val pr_assumptionset : ?flags:PrintingFlags.t ->
  env -> evar_map -> theory_assumptions -> types ContextObjectMap.t -> Pp.t

val pr_typing_flags : Declarations.typing_flags -> Pp.t

module Debug :
sig

val pr_goal : ?flags:PrintingFlags.t -> Proofview.Goal.t -> Pp.t

end
(** Debug printers *)
