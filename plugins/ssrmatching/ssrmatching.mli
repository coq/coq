(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)

open Goal
open Environ
open Evd
open Constr

open Ltac_plugin
open Tacexpr

(** ******** Small Scale Reflection pattern matching facilities ************* *)

(** Pattern parsing *)

(** The type of context patterns, the patterns of the [set] tactic and 
    [:] tactical. These are patterns that identify a precise subterm. *)
type cpattern
val pr_cpattern : cpattern -> Pp.t

(** The type of rewrite patterns, the patterns of the [rewrite] tactic.
    These patterns also include patterns that identify all the subterms
    of a context (i.e. "in" prefix) *)
type rpattern
val pr_rpattern : rpattern -> Pp.t

(** Pattern interpretation and matching *)

exception NoMatch
exception NoProgress

(** AST for [rpattern] (and consequently [cpattern]) *)
type ('ident, 'term) ssrpattern =
  | T of 'term
  | In_T of 'term
  | X_In_T of 'ident * 'term
  | In_X_In_T of 'ident * 'term
  | E_In_X_In_T of 'term * 'ident * 'term
  | E_As_X_In_T of 'term * 'ident * 'term

type pattern = evar_map * (constr, constr) ssrpattern
val pp_pattern : pattern -> Pp.t

(** Extracts the redex and applies to it the substitution part of the pattern.
  @raise Anomaly if called on [In_T] or [In_X_In_T] *)
val redex_of_pattern :
  ?resolve_typeclasses:bool -> env -> pattern ->
     constr Evd.in_evar_universe_context

(** [interp_rpattern ise gl rpat] "internalizes" and "interprets" [rpat]
    in the current [Ltac] interpretation signature [ise] and tactic input [gl]*)
val interp_rpattern :
  goal sigma ->
  rpattern ->
    pattern

(** [interp_cpattern ise gl cpat ty] "internalizes" and "interprets" [cpat]
    in the current [Ltac] interpretation signature [ise] and tactic input [gl].
    [ty] is an optional type for the redex of [cpat] *)
val interp_cpattern :
  goal sigma ->
  cpattern -> (glob_constr_and_expr * Geninterp.interp_sign) option ->
    pattern

(** The set of occurrences to be matched. The boolean is set to true
 *  to signal the complement of this set (i.e. \{-1 3\}) *)
type occ = (bool * int list) option

(** [subst e p t i]. [i] is the number of binders
    traversed so far, [p] the term from the pattern, [t] the matched one *)
type subst = env -> constr -> constr -> int -> constr

(** [eval_pattern b env sigma t pat occ subst] maps [t] calling [subst] on every
    [occ] occurrence of [pat]. The [int] argument is the number of 
    binders traversed. If [pat] is [None] then then subst is called on [t].
    [t] must live in [env] and [sigma], [pat] must have been interpreted in 
    (an extension of) [sigma]. 
  @raise NoMatch if [pat] has no occurrence and [b] is [true] (default [false])
  @return [t] where all [occ] occurrences of [pat] have been mapped using
    [subst] *)
val eval_pattern :
  ?raise_NoMatch:bool ->
  env -> evar_map -> constr ->
  pattern option -> occ -> subst ->
    constr

(** [fill_occ_pattern b env sigma t pat occ h] is a simplified version of 
    [eval_pattern]. 
    It replaces all [occ] occurrences of [pat] in [t] with Rel [h]. 
    [t] must live in [env] and [sigma], [pat] must have been interpreted in 
    (an extension of) [sigma]. 
  @raise NoMatch if [pat] has no occurrence and [b] is [true] (default [false]) 
  @return the instance of the redex of [pat] that was matched and [t]
    transformed as described above. *)
val fill_occ_pattern :
  ?raise_NoMatch:bool ->
  env -> evar_map -> constr ->
  pattern -> occ -> int ->
    constr Evd.in_evar_universe_context * constr

(** *************************** Low level APIs ****************************** *)

(* The primitive matching facility. It matches of a term with holes, like 
   the T pattern above, and calls a continuation on its occurrences. *)

type ssrdir = L2R | R2L
val pr_dir_side : ssrdir -> Pp.t

(** a pattern for a term with wildcards *)
type tpattern

(** [mk_tpattern env sigma0 sigma_p ok p_origin dir t] compiles a term [t] 
    living in [env] [sigma] (an extension of [sigma0]) intro a [tpattern].
    The [tpattern] can hold a (proof) term [p] and a diction [dir]. The [ok]
    callback is used to filter occurrences.
  @return the compiled [tpattern] and its [evar_map]
  @raise UserEerror is the pattern is a wildcard *)
val mk_tpattern :
  ?p_origin:ssrdir * constr ->
  env -> evar_map ->
  evar_map * constr ->
  (constr -> evar_map -> bool) ->
  ssrdir -> constr ->
    evar_map * tpattern

(** [findP env t i k] is a stateful function that finds the next occurrence 
    of a tpattern and calls the callback [k] to map the subterm matched. 
    The [int] argument passed to [k] is the number of binders traversed so far 
    plus the initial value [i]. 
  @return [t] where the subterms identified by the selected occurrences of 
    the patter have been mapped using [k]
  @raise NoMatch if the raise_NoMatch flag given to [mk_tpattern_matcher] is
    [true] and if the pattern did not match 
  @raise UserEerror if the raise_NoMatch flag given to [mk_tpattern_matcher] is
    [false] and if the pattern did not match *)
type find_P =
  env -> constr -> int -> k:subst -> constr

(** [conclude ()] asserts that all mentioned ocurrences have been visited.
  @return the instance of the pattern, the evarmap after the pattern
    instantiation, the proof term and the ssrdit stored in the tpattern
  @raise UserEerror if too many occurrences were specified *)
type conclude =
  unit -> constr * ssrdir * (evar_map * UState.t * constr)

(** [mk_tpattern_matcher b o sigma0 occ sigma_tplist] creates a pair 
    a function [find_P] and [conclude] with the behaviour explained above.
    The flag [b] (default [false]) changes the error reporting behaviour
    of [find_P] if none of the [tpattern] matches. The argument [o] can
    be passed to tune the [UserError] eventually raised (useful if the 
    pattern is coming from the LHS/RHS of an equation) *)
val mk_tpattern_matcher :
  ?all_instances:bool ->
  ?raise_NoMatch:bool ->
  ?upats_origin:ssrdir * constr ->
  evar_map -> occ -> evar_map * tpattern list ->
    find_P * conclude

(** Example of [mk_tpattern_matcher] to implement 
    [rewrite \{occ\}\[in t\]rules].
    It first matches "in t" (called [pat]), then in all matched subterms 
    it matches the LHS of the rules using [find_R].
    [concl0] is the initial goal, [concl] will be the goal where some terms
    are replaced by a De Bruijn index. The [rw_progress] extra check
    selects only occurrences that are not rewritten to themselves (e.g.
    an occurrence "x + x" rewritten with the commutativity law of addition 
    is skipped) {[
  let find_R, conclude = match pat with
  | Some (_, In_T _) ->
      let aux (sigma, pats) (d, r, lhs, rhs) =
        let sigma, pat = 
          mk_tpattern env0 sigma0 (sigma, r) (rw_progress rhs) d lhs in
        sigma, pats @ [pat] in
      let rpats = List.fold_left aux (r_sigma, []) rules in
      let find_R, end_R = mk_tpattern_matcher sigma0 occ rpats in
      find_R ~k:(fun _ _ h -> mkRel h), 
      fun cl -> let rdx, d, r = end_R () in (d,r),rdx
  | _ -> ... in
  let concl = eval_pattern env0 sigma0 concl0 pat occ find_R in
  let (d, r), rdx = conclude concl in ]} *)

(* convenience shortcut: [pf_fill_occ_term gl occ (sigma,t)] returns
 * the conclusion of [gl] where [occ] occurrences of [t] have been replaced
 * by [Rel 1] and the instance of [t] *)
val pf_fill_occ_term : goal sigma -> occ -> evar_map * EConstr.t -> EConstr.t * EConstr.t

(* It may be handy to inject a simple term into the first form of cpattern *)
val cpattern_of_term : char * glob_constr_and_expr -> Geninterp.interp_sign -> cpattern

(** Helpers to make stateful closures. Example: a [find_P] function may be 
    called many times, but the pattern instantiation phase is performed only the
    first time. The corresponding [conclude] has to return the instantiated
    pattern redex. Since it is up to [find_P] to raise [NoMatch] if the pattern
    has no instance, [conclude] considers it an anomaly if the pattern did
    not match *)

(** [do_once r f] calls [f] and updates the ref only once *)
val do_once : 'a option ref -> (unit -> 'a) -> unit
(** [assert_done r] return the content of r. @raise Anomaly is r is [None] *)
val assert_done : 'a option ref -> 'a

(** Very low level APIs.
    these are calls to evarconv's [the_conv_x] followed by
    [solve_unif_constraints_with_heuristics] and [resolve_typeclasses].
    In case of failure they raise [NoMatch] *)

val unify_HO : env -> evar_map -> EConstr.constr -> EConstr.constr -> evar_map
val pf_unify_HO : goal sigma -> EConstr.constr -> EConstr.constr -> goal sigma

(** Some more low level functions needed to implement the full SSR language
    on top of the former APIs *)
val tag_of_cpattern : cpattern -> char
val loc_of_cpattern : cpattern -> Loc.t option
val id_of_pattern : pattern -> Names.Id.t option
val is_wildcard : cpattern -> bool
val cpattern_of_id : Names.Id.t -> cpattern
val pr_constr_pat : constr -> Pp.t
val pf_merge_uc : UState.t -> goal Evd.sigma -> goal Evd.sigma
val pf_unsafe_merge_uc : UState.t -> goal Evd.sigma -> goal Evd.sigma

(* One can also "Set SsrMatchingDebug" from a .v *)
val debug : bool -> unit

(* One should delimit a snippet with "Set SsrMatchingProfiling" and
 * "Unset SsrMatchingProfiling" to get timings *)
val profile : bool -> unit

val ssrinstancesof : cpattern -> Tacmach.tactic

(** Functions used for grammar extensions. Do not use. *)

module Internal :
sig
  val wit_rpatternty : (rpattern, rpattern, rpattern) Genarg.genarg_type
  val glob_rpattern : Genintern.glob_sign -> rpattern -> rpattern
  val subst_rpattern : Mod_subst.substitution -> rpattern -> rpattern
  val interp_rpattern : Geninterp.interp_sign -> Proof_type.goal Evd.sigma -> rpattern -> Evd.evar_map * rpattern
  val pr_rpattern : rpattern -> Pp.t
  val mk_rpattern : (cpattern, cpattern) ssrpattern -> rpattern
  val mk_lterm : Constrexpr.constr_expr -> Geninterp.interp_sign option -> cpattern
  val mk_term : char -> Constrexpr.constr_expr -> Geninterp.interp_sign option -> cpattern

  val glob_cpattern : Genintern.glob_sign -> cpattern -> cpattern
  val subst_ssrterm : Mod_subst.substitution -> cpattern -> cpattern
  val interp_ssrterm : Geninterp.interp_sign -> Proof_type.goal Evd.sigma -> cpattern -> Evd.evar_map * cpattern
  val pr_ssrterm : cpattern -> Pp.t
end

(* eof *)
