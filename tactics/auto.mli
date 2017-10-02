(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This files implements auto and related automation tactics *)

open Names
open EConstr
open Pattern
open Hints
open Tactypes

(* This generic value type is used internally to allow for the interpretation
  of tactic arguments to `Hint Extern If self`. Do not use. *)
val val_callback : unit Proofview.tactic Geninterp.Val.typ

val compute_secvars : Proofview.Goal.t -> Id.Pred.t

val default_search_depth : int ref

val auto_flags_of_state : TransparentState.t -> Unification.unify_flags

(** Try unification with the precompiled clause, then use registered Apply *)
val unify_resolve : Unification.unify_flags -> hint -> unit Proofview.tactic

(** Generic [conclPattern]:
  @aises Constr_matching.PatternMatchingFailure in case the conclusion does not match the pattern.

  Otherwise returns the bindings of pattern variables in the pattern extending the given ist, if any.
  *)
val conclPattern_gen : Environ.env -> Evd.evar_map -> ?ist:Geninterp.Val.t Id.Map.t ->
  constr -> constr_pattern option -> Geninterp.Val.t Id.Map.t

(** [ConclPattern self concl pat ist iftac thentac cont]:
  if the term concl matches the pattern pat, (in sense of
  [Pattern.somatches], then replace [?1] [?2] metavars in iftac and thentac by the
  right values to build tactics.
  If [self] is given, then it also binds it to [cont] when evaluating the tactics.
  If [iftac] is given, then the resulting tactic is `tclIFCATCH iftac thentac cont`
*)

val conclPattern : Environ.env -> Evd.evar_map -> Names.Id.t CAst.t option ->
  constr -> constr_pattern option ->
  Genarg.glob_generic_argument option -> Genarg.glob_generic_argument ->
  unit hint_tactic

(** The Auto tactic *)

(** The use of the "core" database can be de-activated by passing
    "nocore" amongst the databases. *)

val auto : ?debug:debug ->
  int -> delayed_open_constr list -> hint_db_name list -> unit Proofview.tactic

(** Auto with more delta. *)

(** auto with default search depth and with the hint database "core" *)
val default_auto : unit Proofview.tactic

(** auto with all hint databases *)
val full_auto : ?debug:debug ->
  int -> delayed_open_constr list -> unit Proofview.tactic

(** auto with default search depth and with all hint databases *)
val default_full_auto : unit Proofview.tactic

(** The generic form of auto (second arg [None] means all bases) *)
val gen_auto : ?debug:debug ->
  int option -> delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic

(** The hidden version of auto *)
val h_auto   : ?debug:debug ->
  int option -> delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic

(** Trivial *)

val trivial : ?debug:debug ->
  delayed_open_constr list -> hint_db_name list -> unit Proofview.tactic
val gen_trivial : ?debug:debug ->
  delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic
val full_trivial : ?debug:debug ->
  delayed_open_constr list -> unit Proofview.tactic
val h_trivial : ?debug:debug ->
  delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic
