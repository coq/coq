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
open Constr

type 'a obligation_body = DefinedObl of 'a | TermObl of constr

type obligation =
  { obl_name : Id.t
  ; obl_type : types
  ; obl_location : Evar_kinds.t Loc.located
  ; obl_body : pconstant obligation_body option
  ; obl_status : bool * Evar_kinds.obligation_definition_status
  ; obl_deps : Int.Set.t
  ; obl_tac : unit Proofview.tactic option }

type obligations = obligation array * int

type notations =
  (lstring * Constrexpr.constr_expr * Notation_term.scope_name option) list

type fixpoint_kind =
  | IsFixpoint of lident option list
  | IsCoFixpoint

type program_info =
  { prg_name : Id.t
  ; prg_body : constr
  ; prg_type : constr
  ; prg_ctx : UState.t
  ; prg_univdecl : UState.universe_decl
  ; prg_obligations : obligations
  ; prg_deps : Id.t list
  ; prg_fixkind : fixpoint_kind option
  ; prg_implicits : Impargs.manual_implicits
  ; prg_notations : notations
  ; prg_poly : bool
  ; prg_scope : DeclareDef.locality
  ; prg_kind : Decl_kinds.definition_object_kind
  ; prg_reduce : constr -> constr
  ; prg_hook : DeclareDef.Hook.t option
  ; prg_opaque : bool
  ; prg_sign : Environ.named_context_val }

val declare_obligation :
     program_info
  -> obligation
  -> Constr.types
  -> Constr.types option
  -> Entries.universes_entry
  -> bool * obligation
(** [declare_obligation] Save an obligation *)

module ProgMap : CMap.ExtS with type key = Id.t and module Set := Id.Set

val declare_definition : program_info -> Names.GlobRef.t

type progress =
  (* Resolution status of a program *)
  | Remain of int
  (* n obligations remaining *)
  | Dependent
  (* Dependent on other definitions *)
  | Defined of GlobRef.t
  (* Defined as id *)

type obligation_qed_info =
  { name : Id.t
  ; num : int
  ; auto : Id.t option -> Int.Set.t -> unit Proofview.tactic option -> progress
  }

val obligation_terminator
  : Evd.side_effects Proof_global.proof_entry list
  -> UState.t
  -> obligation_qed_info -> unit
(** [obligation_terminator] part 2 of saving an obligation *)

val update_obls :
     program_info
  -> obligation array
  -> int
  -> progress
(** [update_obls prg obls n progress] What does this do? *)

(** { 2 Util }  *)

val get_prg_info_map : unit -> program_info CEphemeron.key ProgMap.t

val program_tcc_summary_tag :
  program_info CEphemeron.key Id.Map.t Summary.Dyn.tag

val obl_substitution :
     bool
  -> obligation array
  -> Int.Set.t
  -> (ProgMap.key * (Constr.types * Constr.types)) list

val dependencies : obligation array -> int -> Int.Set.t

val err_not_transp : unit -> unit
val progmap_add : ProgMap.key -> program_info CEphemeron.key -> unit

(* This is a hack to make it possible for Obligations to craft a Qed
 * behind the scenes.  The fix_exn the Stm attaches to the Future proof
 * is not available here, so we provide a side channel to get it *)
val stm_get_fix_exn : (unit -> Exninfo.iexn -> Exninfo.iexn) Hook.t
