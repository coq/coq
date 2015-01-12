(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Term
open Context
open Environ
open Globnames
open Decl_kinds
open Evd
open Misctypes
open Clenv
open Pattern
open Vernacexpr

(** {6 General functions. } *)

exception Bound

val decompose_app_bound : constr -> global_reference * constr array

(** Pre-created hint databases *)

type 'a auto_tactic =
  | Res_pf     of 'a (* Hint Apply *)
  | ERes_pf    of 'a (* Hint EApply *)
  | Give_exact of 'a
  | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
  | Unfold_nth of evaluable_global_reference       (* Hint Unfold *)
  | Extern     of Tacexpr.glob_tactic_expr       (* Hint Extern *)

type hints_path_atom = 
  | PathHints of global_reference list
  | PathAny

type 'a gen_auto_tactic = {
  pri   : int;            (** A number between 0 and 4, 4 = lower priority *)
  poly  : polymorphic;    (** Is the hint polymorpic and hence should be refreshed at each application *)
  pat   : constr_pattern option; (** A pattern for the concl of the Goal *)
  name  : hints_path_atom; (** A potential name to refer to the hint *) 
  code  : 'a auto_tactic; (** the tactic to apply when the concl matches pat *)
}

type pri_auto_tactic = (constr * clausenv) gen_auto_tactic

type search_entry

(** The head may not be bound. *)

type hint_entry = global_reference option * 
  (constr * types * Univ.universe_context_set) gen_auto_tactic

type hints_path =
  | PathAtom of hints_path_atom
  | PathStar of hints_path
  | PathSeq of hints_path * hints_path
  | PathOr of hints_path * hints_path
  | PathEmpty
  | PathEpsilon

val normalize_path : hints_path -> hints_path
val path_matches : hints_path -> hints_path_atom list -> bool
val path_derivate : hints_path -> hints_path_atom -> hints_path
val pp_hints_path : hints_path -> Pp.std_ppcmds

module Hint_db :
  sig
    type t
    val empty : transparent_state -> bool -> t
    val find : global_reference -> t -> search_entry
    val map_none : t -> pri_auto_tactic list

    (** All hints associated to the reference *)
    val map_all : global_reference -> t -> pri_auto_tactic list

    (** All hints associated to the reference, respecting modes if evars appear in the 
	arguments, _not_ using the discrimination net. *)
    val map_existential : (global_reference * constr array) -> constr -> t -> pri_auto_tactic list

    (** All hints associated to the reference, respecting modes if evars appear in the 
	arguments and using the discrimination net. *)
    val map_eauto : (global_reference * constr array) -> constr -> t -> pri_auto_tactic list

    (** All hints associated to the reference, respecting modes if evars appear in the 
	arguments. *)
    val map_auto : (global_reference * constr array) -> constr -> t -> pri_auto_tactic list

    val add_one : hint_entry -> t -> t
    val add_list : (hint_entry) list -> t -> t
    val remove_one : global_reference -> t -> t
    val remove_list : global_reference list -> t -> t
    val iter : (global_reference option -> bool array list -> pri_auto_tactic list -> unit) -> t -> unit

    val use_dn : t -> bool
    val transparent_state : t -> transparent_state
    val set_transparent_state : t -> transparent_state -> t

    val add_cut : hints_path -> t -> t
    val cut : t -> hints_path

    val unfolds : t -> Id.Set.t * Cset.t
  end

type hint_db_name = string

type hint_db = Hint_db.t

type hnf = bool

type hint_term =
  | IsGlobRef of global_reference
  | IsConstr of constr * Univ.universe_context_set

type hints_entry =
  | HintsResolveEntry of (int option * polymorphic * hnf * hints_path_atom * 
			  hint_term) list
  | HintsImmediateEntry of (hints_path_atom * polymorphic * hint_term) list
  | HintsCutEntry of hints_path
  | HintsUnfoldEntry of evaluable_global_reference list
  | HintsTransparencyEntry of evaluable_global_reference list * bool
  | HintsModeEntry of global_reference * bool list      
  | HintsExternEntry of
      int * (patvar list * constr_pattern) option * Tacexpr.glob_tactic_expr

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

val prepare_hint : bool (* Check no remaining evars *) -> env -> evar_map -> 
  open_constr -> hint_term

(** [make_exact_entry pri (c, ctyp)].
   [c] is the term given as an exact proof to solve the goal;
   [ctyp] is the type of [c]. *)

val make_exact_entry : env -> evar_map -> int option -> polymorphic -> ?name:hints_path_atom -> 
  (constr * types * Univ.universe_context_set) -> hint_entry

(** [make_apply_entry (eapply,hnf,verbose) pri (c,cty)].
   [eapply] is true if this hint will be used only with EApply;
   [hnf] should be true if we should expand the head of cty before searching for
   products;
   [c] is the term given as an exact proof to solve the goal;
   [cty] is the type of [c]. *)

val make_apply_entry :
  env -> evar_map -> bool * bool * bool -> int option -> polymorphic -> ?name:hints_path_atom -> 
  (constr * types * Univ.universe_context_set) -> hint_entry

(** A constr which is Hint'ed will be:
   - (1) used as an Exact, if it does not start with a product
   - (2) used as an Apply, if its HNF starts with a product, and
         has no missing arguments.
   - (3) used as an EApply, if its HNF starts with a product, and
         has missing arguments. *)

val make_resolves :
  env -> evar_map -> bool * bool * bool -> int option -> polymorphic -> ?name:hints_path_atom -> 
  hint_term -> hint_entry list

(** [make_resolve_hyp hname htyp].
   used to add an hypothesis to the local hint database;
   Never raises a user exception;
   If the hyp cannot be used as a Hint, the empty list is returned. *)

val make_resolve_hyp :
  env -> evar_map -> named_declaration -> hint_entry list

(** [make_extern pri pattern tactic_expr] *)

val make_extern :
  int -> constr_pattern option -> Tacexpr.glob_tactic_expr
      -> hint_entry

val extern_intern_tac :
  (patvar list -> Tacexpr.raw_tactic_expr -> Tacexpr.glob_tactic_expr) Hook.t

(** Create a Hint database from the pairs (name, constr).
   Useful to take the current goal hypotheses as hints;
   Boolean tells if lemmas with evars are allowed *)

val make_local_hint_db : env -> evar_map -> ?ts:transparent_state -> bool -> open_constr list -> hint_db

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
val pr_autotactic : (constr * 'a) auto_tactic -> Pp.std_ppcmds

(** Hook for changing the initialization of auto *)

val add_hints_init : (unit -> unit) -> unit

