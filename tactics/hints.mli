(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open EConstr
open Environ
open Evd
open Tactypes
open Typeclasses

(** {6 General functions. } *)

exception Bound

val decompose_app_bound : evar_map -> constr -> GlobRef.t * constr array

type debug = Debug | Info | Off

val secvars_of_hyps : ('c, 't) Context.Named.pt -> Id.Pred.t

val empty_hint_info : 'a Typeclasses.hint_info_gen

val hint_cat : Libobject.category

(** Pre-created hint databases *)

type 'a hint_ast =
  | Res_pf     of 'a (* Hint Apply *)
  | ERes_pf    of 'a (* Hint EApply *)
  | Give_exact of 'a
  | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
  | Unfold_nth of Tacred.evaluable_global_reference       (* Hint Unfold *)
  | Extern     of Pattern.constr_pattern option * Genarg.glob_generic_argument       (* Hint Extern *)

type hint

val hint_as_term : hint -> Univ.ContextSet.t option * constr

type 'a hints_path_atom_gen =
  | PathHints of 'a list
  (* For forward hints, their names is the list of projections *)
  | PathAny

type hints_path_atom = GlobRef.t hints_path_atom_gen
type hint_db_name = string

module FullHint :
sig
  type t
  val priority : t -> int
  val pattern : t -> Pattern.constr_pattern option
  val database : t -> string option
  val run : t -> (hint hint_ast -> 'r Proofview.tactic) -> 'r Proofview.tactic
  val name : t -> hints_path_atom
  val print : env -> evar_map -> t -> Pp.t
  val subgoals : t -> int option

  (** This function is for backward compatibility only, not to use in newly
    written code. *)
  val repr : t -> hint hint_ast
end

(** The head may not be bound. *)

type hint_mode =
  | ModeInput (* No evars *)
  | ModeNoHeadEvar (* No evar at the head *)
  | ModeOutput (* Anything *)

type 'a hints_transparency_target =
  | HintsVariables
  | HintsConstants
  | HintsReferences of 'a list

type 'a hints_path_gen =
  | PathAtom of 'a hints_path_atom_gen
  | PathStar of 'a hints_path_gen
  | PathSeq of 'a hints_path_gen * 'a hints_path_gen
  | PathOr of 'a hints_path_gen * 'a hints_path_gen
  | PathEmpty
  | PathEpsilon

type pre_hints_path = Libnames.qualid hints_path_gen
type hints_path = GlobRef.t hints_path_gen

val normalize_path : hints_path -> hints_path
val path_matches : hints_path -> hints_path_atom list -> bool
val path_derivate : hints_path -> hints_path_atom -> hints_path
val pp_hints_path_gen : ('a -> Pp.t) -> 'a hints_path_gen -> Pp.t
val pp_hints_path_atom : ('a -> Pp.t) -> 'a hints_path_atom_gen -> Pp.t
val pp_hints_path : hints_path -> Pp.t
val pp_hint_mode : hint_mode -> Pp.t
val glob_hints_path_atom :
  Libnames.qualid hints_path_atom_gen -> GlobRef.t hints_path_atom_gen
val glob_hints_path :
  Libnames.qualid hints_path_gen -> GlobRef.t hints_path_gen

type mode_match =
  | NoMode
  | WithMode of hint_mode array

type 'a with_mode =
  | ModeMatch of mode_match * 'a
  | ModeMismatch

module Hint_db :
  sig
    type t
    val empty : ?name:hint_db_name -> TransparentState.t -> bool -> t

    (** All hints which have no pattern.
     * [secvars] represent the set of section variables that
     * can be used in the hint. *)
    val map_none : secvars:Id.Pred.t -> t -> FullHint.t list

    (** All hints associated to the reference *)
    val map_all : secvars:Id.Pred.t -> GlobRef.t -> t -> FullHint.t list

    (** All hints associated to the reference, respecting modes if evars appear in the
        arguments and using the discrimination net.
        Returns a [ModeMismatch] if there are declared modes and none matches. *)
    val map_eauto : env -> evar_map -> secvars:Id.Pred.t -> (GlobRef.t * constr array) -> constr -> t -> FullHint.t list with_mode

    (** All hints associated to the reference.
        Precondition: no evars should appear in the arguments, so no modes
        are checked. *)
    val map_auto : env -> evar_map -> secvars:Id.Pred.t ->
       (GlobRef.t * constr array) -> constr -> t -> FullHint.t list

    val remove_one : Environ.env -> GlobRef.t -> t -> t
    val remove_list : Environ.env -> GlobRef.t list -> t -> t
    val iter : (GlobRef.t option ->
                hint_mode array list -> FullHint.t list -> unit) -> t -> unit

    val fold : (GlobRef.t option -> hint_mode array list -> FullHint.t list -> 'a -> 'a) -> t -> 'a -> 'a

    val use_dn : t -> bool
    val transparent_state : t -> TransparentState.t
    val set_transparent_state : t -> TransparentState.t -> t

    val add_cut : hints_path -> t -> t
    val cut : t -> hints_path

    val unfolds : t -> Id.Set.t * Cset.t

    val add_modes : hint_mode array list GlobRef.Map.t -> t -> t
    val modes : t -> hint_mode array list GlobRef.Map.t
  end

type hint_db = Hint_db.t

type hnf = bool

type hint_term

type hints_entry =
  | HintsResolveEntry of (hint_info * hnf * hints_path_atom * hint_term) list
  | HintsImmediateEntry of (hints_path_atom * hint_term) list
  | HintsCutEntry of hints_path
  | HintsUnfoldEntry of Tacred.evaluable_global_reference list
  | HintsTransparencyEntry of Tacred.evaluable_global_reference hints_transparency_target * bool
  | HintsModeEntry of GlobRef.t * hint_mode list
  | HintsExternEntry of hint_info * Genarg.glob_generic_argument

val searchtable_map : hint_db_name -> hint_db

val searchtable_add : (hint_db_name * hint_db) -> unit

type hint_locality = Local | Export | SuperGlobal

val default_hint_locality : unit -> hint_locality
(** Warns *)

(** [create_hint_db local name st use_dn].
   [st] is a transparency state for unification using this db
   [use_dn] switches the use of the discrimination net for all hints
   and patterns. *)

val create_hint_db : bool -> hint_db_name -> TransparentState.t -> bool -> unit

val remove_hints : locality:hint_locality -> hint_db_name list -> GlobRef.t list -> unit

val current_db_names : unit -> String.Set.t

val current_pure_db : unit -> hint_db list

val add_hints : locality:hint_locality -> hint_db_name list -> hints_entry -> unit

val hint_globref : GlobRef.t -> hint_term

val hint_constr : constr * Univ.ContextSet.t option -> hint_term
[@ocaml.deprecated "Declare a hint constant instead"]

(** A constr which is Hint'ed will be:
   - (1) used as an Exact, if it does not start with a product
   - (2) used as an Apply, if its HNF starts with a product, and
         has no missing arguments.
   - (3) used as an EApply, if its HNF starts with a product, and
         has missing arguments. *)

val push_resolves :
  env -> evar_map -> GlobRef.t -> Hint_db.t -> Hint_db.t

(** [push_resolve_hyp hname htyp db].
   used to add an hypothesis to the local hint database;
   Never raises a user exception;
   If the hyp cannot be used as a Hint, it is not added. *)

val push_resolve_hyp :
  env -> evar_map -> Id.t -> Hint_db.t -> Hint_db.t

(** Create a Hint database from the pairs (name, constr).
   Useful to take the current goal hypotheses as hints;
   Boolean tells if lemmas with evars are allowed *)

val make_local_hint_db : env -> evar_map -> ?ts:TransparentState.t -> bool -> delayed_open_constr list -> hint_db

val make_db_list : hint_db_name list -> hint_db list

val wrap_hint_warning : 'a Proofview.tactic -> 'a Proofview.tactic
(** Use around toplevel calls to hint-using tactics, to enable the tracking of
    non-imported hints. Any tactic calling [run_hint] must be wrapped this
    way. *)

val wrap_hint_warning_fun : env -> evar_map ->
  (evar_map -> 'a * evar_map) -> 'a * evar_map
(** Variant of the above for non-tactics *)

val fresh_hint : env -> evar_map -> hint -> evar_map * constr

val hint_res_pf : ?with_evars:bool -> ?with_classes:bool ->
  ?flags:Unification.unify_flags -> hint -> unit Proofview.tactic

(** Printing  hints *)

val pr_searchtable : env -> evar_map -> Pp.t
val pr_applicable_hint : Proof.t -> Pp.t
val pr_hint_ref : env -> evar_map -> GlobRef.t -> Pp.t
val pr_hint_db_by_name : env -> evar_map -> hint_db_name -> Pp.t
val pr_hint_db_env : env -> evar_map -> Hint_db.t -> Pp.t
