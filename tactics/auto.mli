(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Proof_type
open Tacmach
open Clenv
open Pattern
open Environ
open Evd
open Libnames
open Vernacexpr
open Mod_subst
(*i*)

type auto_tactic =
  | Res_pf     of constr * clausenv    (* Hint Apply *)
  | ERes_pf    of constr * clausenv    (* Hint EApply *)
  | Give_exact of constr
  | Res_pf_THEN_trivial_fail of constr * clausenv (* Hint Immediate *)
  | Unfold_nth of evaluable_global_reference          (* Hint Unfold *)
  | Extern     of Tacexpr.glob_tactic_expr   (* Hint Extern *)

open Rawterm

type pri_auto_tactic = {
  pri   : int;            (* A number between 0 and 4, 4 = lower priority *)
  pat   : constr_pattern option; (* A pattern for the concl of the Goal *)
  code  : auto_tactic;    (* the tactic to apply when the concl matches pat *)
}

type stored_data = pri_auto_tactic

type search_entry

(* The head may not be bound. *)

type hint_entry = global_reference option * pri_auto_tactic

module Hint_db :
  sig
    type t
    val empty : transparent_state -> bool -> t
    val find : global_reference -> t -> search_entry
    val map_none : t -> pri_auto_tactic list
    val map_all : global_reference -> t -> pri_auto_tactic list
    val map_auto : global_reference * constr -> t -> pri_auto_tactic list
    val add_one : hint_entry -> t -> t
    val add_list : (hint_entry) list -> t -> t
    val iter : (global_reference option -> stored_data list -> unit) -> t -> unit

    val use_dn : t -> bool
    val transparent_state : t -> transparent_state
    val set_transparent_state : t -> transparent_state -> t

    val unfolds : t -> Idset.t * Cset.t
  end

type hint_db_name = string

type hint_db = Hint_db.t

type hints_entry =
  | HintsResolveEntry of (int option * bool * constr) list
  | HintsImmediateEntry of constr list
  | HintsUnfoldEntry of evaluable_global_reference list
  | HintsTransparencyEntry of evaluable_global_reference list * bool
  | HintsExternEntry of
      int * (patvar list * constr_pattern) option * Tacexpr.glob_tactic_expr
  | HintsDestructEntry of identifier * int * (bool,unit) Tacexpr.location *
      (patvar list * constr_pattern) * Tacexpr.glob_tactic_expr

val searchtable_map : hint_db_name -> hint_db

val searchtable_add : (hint_db_name * hint_db) -> unit

(* [create_hint_db local name st use_dn].
   [st] is a transparency state for unification using this db
   [use_dn] switches the use of the discrimination net for all hints
   and patterns. *)

val create_hint_db : bool -> hint_db_name -> transparent_state -> bool -> unit

val current_db_names : unit -> hint_db_name list

val interp_hints : hints_expr -> hints_entry

val add_hints : locality_flag -> hint_db_name list -> hints_entry -> unit

val print_searchtable : unit -> unit

val print_applicable_hint : unit -> unit

val print_hint_ref : global_reference -> unit

val print_hint_db_by_name : hint_db_name -> unit

val print_hint_db : Hint_db.t -> unit

(* [make_exact_entry pri (c, ctyp)].
   [c] is the term given as an exact proof to solve the goal;
   [ctyp] is the type of [c]. *)

val make_exact_entry : evar_map -> int option -> constr * constr -> hint_entry

(* [make_apply_entry (eapply,verbose) pri (c,cty)].
   [eapply] is true if this hint will be used only with EApply;
   [hnf] should be true if we should expand the head of cty before searching for
   products;
   [c] is the term given as an exact proof to solve the goal;
   [cty] is the type of [c]. *)

val make_apply_entry :
  env -> evar_map -> bool * bool * bool -> int option -> constr * constr
      -> hint_entry

(* A constr which is Hint'ed will be:
   (1) used as an Exact, if it does not start with a product
   (2) used as an Apply, if its HNF starts with a product, and
       has no missing arguments.
   (3) used as an EApply, if its HNF starts with a product, and
       has missing arguments. *)

val make_resolves :
  env -> evar_map -> bool * bool * bool -> int option -> constr ->
      hint_entry list

(* [make_resolve_hyp hname htyp].
   used to add an hypothesis to the local hint database;
   Never raises a user exception;
   If the hyp cannot be used as a Hint, the empty list is returned. *)

val make_resolve_hyp :
  env -> evar_map -> named_declaration -> hint_entry list

(* [make_extern pri pattern tactic_expr] *)

val make_extern :
  int -> constr_pattern option -> Tacexpr.glob_tactic_expr
      -> hint_entry

val set_extern_interp :
  (patvar_map -> Tacexpr.glob_tactic_expr -> tactic) -> unit

val set_extern_intern_tac :
  (patvar list -> Tacexpr.raw_tactic_expr -> Tacexpr.glob_tactic_expr)
  -> unit

val set_extern_subst_tactic :
  (substitution -> Tacexpr.glob_tactic_expr -> Tacexpr.glob_tactic_expr)
  -> unit

(* Create a Hint database from the pairs (name, constr).
   Useful to take the current goal hypotheses as hints;
   Boolean tells if lemmas with evars are allowed *)

val make_local_hint_db : bool -> constr list -> goal sigma -> hint_db

val priority : ('a * pri_auto_tactic) list -> ('a * pri_auto_tactic) list

val default_search_depth : int ref

val auto_unif_flags : Unification.unify_flags

(* Try unification with the precompiled clause, then use registered Apply *)
val unify_resolve_nodelta : (constr * clausenv) -> tactic

val unify_resolve : Unification.unify_flags -> (constr * clausenv) -> tactic

(* [ConclPattern concl pat tacast]:
   if the term concl matches the pattern pat, (in sense of
   [Pattern.somatches], then replace [?1] [?2] metavars in tacast by the
   right values to build a tactic *)

val conclPattern : constr -> constr_pattern option -> Tacexpr.glob_tactic_expr -> tactic

(* The Auto tactic *)

val auto : int -> constr list -> hint_db_name list -> tactic

(* Auto with more delta. *)

val new_auto : int -> constr list -> hint_db_name list -> tactic

(* auto with default search depth and with the hint database "core" *)
val default_auto : tactic

(* auto with all hint databases except the "v62" compatibility database *)
val full_auto : int -> constr list -> tactic

(* auto with all hint databases except the "v62" compatibility database
   and doing delta *)
val new_full_auto : int -> constr list -> tactic

(* auto with default search depth and with all hint databases
   except the "v62" compatibility database *)
val default_full_auto : tactic

(* The generic form of auto (second arg [None] means all bases) *)
val gen_auto : int option -> constr list -> hint_db_name list option -> tactic

(* The hidden version of auto *)
val h_auto   : int option -> constr list -> hint_db_name list option -> tactic

(* Trivial *)
val trivial : constr list -> hint_db_name list -> tactic
val gen_trivial : constr list -> hint_db_name list option -> tactic
val full_trivial : constr list -> tactic
val h_trivial : constr list -> hint_db_name list option -> tactic

val pr_autotactic : auto_tactic -> Pp.std_ppcmds

(*s The following is not yet up to date -- Papageno. *)

(* DAuto *)
val dauto : int option * int option -> constr list -> tactic
val default_search_decomp : int ref
val default_dauto : tactic

val h_dauto : int option * int option -> constr list -> tactic
(* SuperAuto *)

type autoArguments =
  | UsingTDB
  | Destructing

(*
val superauto : int -> (identifier * constr) list -> autoArguments list -> tactic
*)

val h_superauto : int option -> reference list -> bool -> bool -> tactic

val auto_init : (unit -> unit) ref
