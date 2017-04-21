(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open EConstr
open Environ
open Globnames
open Decl_kinds
open Evd
open Misctypes
open Tactypes
open Clenv
open Pattern
open Vernacexpr

(** {6 General functions. } *)

exception Bound

val decompose_app_bound : evar_map -> constr -> global_reference * constr array

type debug = Debug | Info | Off

val secvars_of_hyps : ('c, 't) Context.Named.pt -> Id.Pred.t

val empty_hint_info : 'a hint_info_gen

(** Pre-created hint databases *)

type 'a hint_ast =
  | Res_pf     of 'a (* Hint Apply *)
  | ERes_pf    of 'a (* Hint EApply *)
  | Give_exact of 'a
  | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
  | Unfold_nth of evaluable_global_reference       (* Hint Unfold *)
  | Extern     of Genarg.glob_generic_argument       (* Hint Extern *)

type hint
type raw_hint = constr * types * Univ.universe_context_set

type 'a hints_path_atom_gen =
  | PathHints of 'a list
  (* For forward hints, their names is the list of projections *)
  | PathAny

type hints_path_atom = global_reference hints_path_atom_gen
type hint_db_name = string

type 'a with_metadata = private {
  pri   : int;            (** A number between 0 and 4, 4 = lower priority *)
  poly  : polymorphic;    (** Is the hint polymorpic and hence should be refreshed at each application *)
  pat   : constr_pattern option; (** A pattern for the concl of the Goal *)
  name  : hints_path_atom; (** A potential name to refer to the hint *) 
  db    : hint_db_name option;
  secvars : Id.Pred.t; (** The section variables this hint depends on, as a predicate *)
  code    : 'a; (** the tactic to apply when the concl matches pat *)
}

type full_hint = hint with_metadata

type search_entry

(** The head may not be bound. *)

type hint_entry

type 'a hints_path_gen =
  | PathAtom of 'a hints_path_atom_gen
  | PathStar of 'a hints_path_gen
  | PathSeq of 'a hints_path_gen * 'a hints_path_gen
  | PathOr of 'a hints_path_gen * 'a hints_path_gen
  | PathEmpty
  | PathEpsilon

type pre_hints_path = Libnames.reference hints_path_gen
type hints_path = global_reference hints_path_gen
    
val normalize_path : hints_path -> hints_path
val path_matches : hints_path -> hints_path_atom list -> bool
val path_derivate : hints_path -> hints_path_atom -> hints_path
val pp_hints_path_gen : ('a -> Pp.std_ppcmds) -> 'a hints_path_gen -> Pp.std_ppcmds
val pp_hints_path_atom : ('a -> Pp.std_ppcmds) -> 'a hints_path_atom_gen -> Pp.std_ppcmds
val pp_hints_path : hints_path -> Pp.std_ppcmds
val pp_hint_mode : hint_mode -> Pp.std_ppcmds
val glob_hints_path_atom :
  Libnames.reference hints_path_atom_gen -> Globnames.global_reference hints_path_atom_gen
val glob_hints_path :
  Libnames.reference hints_path_gen -> Globnames.global_reference hints_path_gen

module Hint_db :
  sig
    type t
    val empty : ?name:hint_db_name -> transparent_state -> bool -> t
    val find : global_reference -> t -> search_entry

    (** All hints which have no pattern.
     * [secvars] represent the set of section variables that
     * can be used in the hint. *)
    val map_none : secvars:Id.Pred.t -> t -> full_hint list

    (** All hints associated to the reference *)
    val map_all : secvars:Id.Pred.t -> global_reference -> t -> full_hint list

    (** All hints associated to the reference, respecting modes if evars appear in the 
	arguments, _not_ using the discrimination net. *)
    val map_existential : evar_map -> secvars:Id.Pred.t ->
      (global_reference * constr array) -> constr -> t -> full_hint list

    (** All hints associated to the reference, respecting modes if evars appear in the 
	arguments and using the discrimination net. *)
    val map_eauto : evar_map -> secvars:Id.Pred.t -> (global_reference * constr array) -> constr -> t -> full_hint list

    (** All hints associated to the reference, respecting modes if evars appear in the 
	arguments. *)
    val map_auto : evar_map -> secvars:Id.Pred.t ->
       (global_reference * constr array) -> constr -> t -> full_hint list

    val add_one : env -> evar_map -> hint_entry -> t -> t
    val add_list : env -> evar_map -> hint_entry list -> t -> t
    val remove_one : global_reference -> t -> t
    val remove_list : global_reference list -> t -> t
    val iter : (global_reference option ->
                hint_mode array list -> full_hint list -> unit) -> t -> unit

    val use_dn : t -> bool
    val transparent_state : t -> transparent_state
    val set_transparent_state : t -> transparent_state -> t

    val add_cut : hints_path -> t -> t
    val cut : t -> hints_path

    val unfolds : t -> Id.Set.t * Cset.t
  end

type hint_db = Hint_db.t

type hnf = bool

type hint_info = (patvar list * constr_pattern) hint_info_gen

type hint_term =
  | IsGlobRef of global_reference
  | IsConstr of constr * Univ.universe_context_set

type hints_entry =
  | HintsResolveEntry of
    (hint_info * polymorphic * hnf * hints_path_atom * hint_term) list
  | HintsImmediateEntry of (hints_path_atom * polymorphic * hint_term) list
  | HintsCutEntry of hints_path
  | HintsUnfoldEntry of evaluable_global_reference list
  | HintsTransparencyEntry of evaluable_global_reference list * bool
  | HintsModeEntry of global_reference * hint_mode list
  | HintsExternEntry of hint_info * Genarg.glob_generic_argument

val searchtable_map : hint_db_name -> hint_db

val searchtable_add : (hint_db_name * hint_db) -> unit

(** [create_hint_db local name st use_dn].
   [st] is a transparency state for unification using this db
   [use_dn] switches the use of the discrimination net for all hints
   and patterns. *)

val create_hint_db : bool -> hint_db_name -> transparent_state -> bool -> unit

val remove_hints : bool -> hint_db_name list -> global_reference list -> unit

val current_db_names : unit -> String.Set.t

val current_pure_db : unit -> hint_db list

val interp_hints : polymorphic -> hints_expr -> hints_entry

val add_hints : locality_flag -> hint_db_name list -> hints_entry -> unit

val prepare_hint : bool (* Check no remaining evars *) ->
  (bool * bool) (* polymorphic or monomorphic, local or global *) ->
  env -> evar_map -> evar_map * constr -> hint_term

(** [make_exact_entry info (c, ctyp, ctx)].
   [c] is the term given as an exact proof to solve the goal;
   [ctyp] is the type of [c].
   [ctx] is its (refreshable) universe context. 
   In info:
   [hint_priority] is the hint's desired priority, it is 0 if unspecified
   [hint_pattern] is the hint's desired pattern, it is inferred if not specified
*)

val make_exact_entry : env -> evar_map -> hint_info -> polymorphic -> ?name:hints_path_atom ->
  (constr * types * Univ.universe_context_set) -> hint_entry

(** [make_apply_entry (eapply,hnf,verbose) info (c,cty,ctx))].
   [eapply] is true if this hint will be used only with EApply;
   [hnf] should be true if we should expand the head of cty before searching for
   products;
   [c] is the term given as an exact proof to solve the goal;
   [cty] is the type of [c].
   [ctx] is its (refreshable) universe context. 
   In info:
   [hint_priority] is the hint's desired priority, it is computed as the number of products in [cty]
   if unspecified
   [hint_pattern] is the hint's desired pattern, it is inferred from the conclusion of [cty]
   if not specified
*)

val make_apply_entry :
  env -> evar_map -> bool * bool * bool -> hint_info -> polymorphic -> ?name:hints_path_atom ->
  (constr * types * Univ.universe_context_set) -> hint_entry

(** A constr which is Hint'ed will be:
   - (1) used as an Exact, if it does not start with a product
   - (2) used as an Apply, if its HNF starts with a product, and
         has no missing arguments.
   - (3) used as an EApply, if its HNF starts with a product, and
         has missing arguments. *)

val make_resolves :
  env -> evar_map -> bool * bool * bool -> hint_info -> polymorphic -> ?name:hints_path_atom ->
  hint_term -> hint_entry list

(** [make_resolve_hyp hname htyp].
   used to add an hypothesis to the local hint database;
   Never raises a user exception;
   If the hyp cannot be used as a Hint, the empty list is returned. *)

val make_resolve_hyp :
  env -> evar_map -> named_declaration -> hint_entry list

(** [make_extern pri pattern tactic_expr] *)

val make_extern :
  int -> constr_pattern option -> Genarg.glob_generic_argument
      -> hint_entry

val run_hint : hint ->
  ((raw_hint * clausenv) hint_ast -> 'r Proofview.tactic) -> 'r Proofview.tactic

(** This function is for backward compatibility only, not to use in newly
    written code. *)
val repr_hint : hint -> (raw_hint * clausenv) hint_ast

(** Create a Hint database from the pairs (name, constr).
   Useful to take the current goal hypotheses as hints;
   Boolean tells if lemmas with evars are allowed *)

val make_local_hint_db : env -> evar_map -> ?ts:transparent_state -> bool -> delayed_open_constr list -> hint_db

val make_db_list : hint_db_name list -> hint_db list

(** Initially created hint databases, for typeclasses and rewrite *)

val typeclasses_db : hint_db_name
val rewrite_db : hint_db_name

(** Printing  hints *)

val pr_searchtable : unit -> std_ppcmds
val pr_applicable_hint : unit -> std_ppcmds
val pr_hint_ref : global_reference -> std_ppcmds
val pr_hint_db_by_name : hint_db_name -> std_ppcmds
val pr_hint_db : Hint_db.t -> std_ppcmds
val pr_hint : hint -> Pp.std_ppcmds

(** Hook for changing the initialization of auto *)

val add_hints_init : (unit -> unit) -> unit

