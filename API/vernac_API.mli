(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file should respect the dependency order established
   in Coq. To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done && echo -e "\n## highparsing files" && cat parsing/highparsing.mllib' > API/link
   ```

   Note however that files in intf/ are located manually now as their
   conceptual linking order in the Coq codebase is incorrect (but it
   works due to these files being implementation-free.

   See below in the file for their concrete position.
*)

open Kernel_API
open Intf_API
open Engine_API
open Library_API
open Pretyping_API
open Parsing_API
open Proofs_API

(************************************************************************)
(* Modules from vernac/                                                 *)
(************************************************************************)

module Ppvernac :
sig
  val pr_vernac : Vernacexpr.vernac_expr -> Pp.std_ppcmds
  val pr_rec_definition : (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) -> Pp.std_ppcmds
end

module Lemmas :
sig

  type 'a declaration_hook

  val mk_hook :
    (Decl_kinds.locality -> Globnames.global_reference -> 'a) -> 'a declaration_hook
  val start_proof : Names.Id.t -> ?pl:Proof_global.universe_binders -> Decl_kinds.goal_kind -> Evd.evar_map ->
    ?terminator:(Proof_global.lemma_possible_guards -> unit declaration_hook -> Proof_global.proof_terminator) ->
    ?sign:Environ.named_context_val -> EConstr.types ->
    ?init_tac:unit Proofview.tactic -> ?compute_guard:Proof_global.lemma_possible_guards ->
    unit declaration_hook -> unit
  val call_hook :
    Future.fix_exn -> 'a declaration_hook -> Decl_kinds.locality -> Globnames.global_reference -> 'a
  val save_proof : ?proof:Proof_global.closed_proof -> Vernacexpr.proof_end -> unit
  val get_current_context : unit -> Evd.evar_map * Environ.env
end

module Himsg :
sig
  val explain_refiner_error : Logic.refiner_error -> Pp.std_ppcmds
  val explain_pretype_error : Environ.env -> Evd.evar_map -> Pretype_errors.pretype_error -> Pp.std_ppcmds
end

module ExplainErr :
sig
  val process_vernac_interp_error : ?allow_uncaught:bool -> Util.iexn -> Util.iexn
  val register_additional_error_info : (Util.iexn -> Pp.std_ppcmds option Loc.located option) -> unit
end

module Locality :
sig
  val make_section_locality : bool option -> bool
  module LocalityFixme : sig
    val consume : unit -> bool option
  end
  val make_module_locality : bool option -> bool
end

module Metasyntax :
sig

  val add_token_obj : string -> unit

  type any_entry = AnyEntry : 'a Pcoq.Gram.entry -> any_entry
  val register_grammar : string -> any_entry list -> unit

end

module Search :
sig
  type glob_search_about_item =
                              | GlobSearchSubPattern of Pattern.constr_pattern
                              | GlobSearchString of string
  type filter_function = Globnames.global_reference -> Environ.env -> Constr.t -> bool
  type display_function = Globnames.global_reference -> Environ.env -> Constr.t -> unit
  val search_about_filter : glob_search_about_item -> filter_function
  val module_filter : Names.DirPath.t list * bool -> filter_function
  val generic_search : int option -> display_function -> unit
end

module Obligations :
sig
  val default_tactic : unit Proofview.tactic ref
  val obligation : int * Names.Id.t option * Constrexpr.constr_expr option ->
                   Genarg.glob_generic_argument option -> unit
  val next_obligation : Names.Id.t option -> Genarg.glob_generic_argument option -> unit
  val try_solve_obligation : int -> Names.Id.t option -> unit Proofview.tactic option -> unit
  val try_solve_obligations : Names.Id.t option -> unit Proofview.tactic option -> unit
  val solve_all_obligations : unit Proofview.tactic option -> unit
  val admit_obligations : Names.Id.t option -> unit
  val show_obligations : ?msg:bool -> Names.Id.t option -> unit
  val show_term : Names.Id.t option -> Pp.std_ppcmds
end

module Command :
sig
  open Names
  open Constrexpr
  open Vernacexpr

  type structured_fixpoint_expr = {
    fix_name : Id.t;
    fix_univs : lident list option;
    fix_annot : Id.t Loc.located option;
    fix_binders : local_binder_expr list;
    fix_body : constr_expr option;
    fix_type : constr_expr
  }

  type structured_one_inductive_expr = {
    ind_name : Id.t;
    ind_univs : lident list option;
    ind_arity : constr_expr;
    ind_lc : (Id.t * constr_expr) list
  }

  type structured_inductive_expr =
    local_binder_expr list * structured_one_inductive_expr list

  type recursive_preentry = Names.Id.t list * Constr.t option list * Constr.types list

  type one_inductive_impls

  val do_mutual_inductive :
    (Vernacexpr.one_inductive_expr * Vernacexpr.decl_notation list) list -> Decl_kinds.cumulative_inductive_flag -> Decl_kinds.polymorphic ->
    Decl_kinds.private_flag -> Decl_kinds.recursivity_kind -> unit

  val do_definition : Names.Id.t -> Decl_kinds.definition_kind -> Vernacexpr.lident list option ->
    Constrexpr.local_binder_expr list -> Redexpr.red_expr option -> Constrexpr.constr_expr ->
    Constrexpr.constr_expr option -> unit Lemmas.declaration_hook -> unit

  val do_fixpoint :
    Decl_kinds.locality -> Decl_kinds.polymorphic -> (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list -> unit

  val extract_fixpoint_components : bool ->
    (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list ->
    structured_fixpoint_expr list * Vernacexpr.decl_notation list

  val interp_fixpoint :
    structured_fixpoint_expr list -> Vernacexpr.decl_notation list ->
    recursive_preentry * Vernacexpr.lident list option * UState.t *
      (EConstr.rel_context * Impargs.manual_implicits * int option) list

  val extract_mutual_inductive_declaration_components :
    (Vernacexpr.one_inductive_expr * Vernacexpr.decl_notation list) list ->
    structured_inductive_expr * Libnames.qualid list * Vernacexpr.decl_notation list

  val interp_mutual_inductive :
    structured_inductive_expr -> Vernacexpr.decl_notation list ->
    Decl_kinds.cumulative_inductive_flag ->
    Decl_kinds.polymorphic ->
    Decl_kinds.private_flag -> Decl_kinds.recursivity_kind ->
    Entries.mutual_inductive_entry * Universes.universe_binders * one_inductive_impls list

  val declare_mutual_inductive_with_eliminations :
    Entries.mutual_inductive_entry -> Universes.universe_binders -> one_inductive_impls list ->
    Names.MutInd.t
end

module Classes :
sig
  val set_typeclass_transparency : Names.evaluable_global_reference -> bool -> bool -> unit
  val new_instance :
    ?abstract:bool ->
    ?global:bool ->
    ?refine:bool ->
    Decl_kinds.polymorphic ->
    Constrexpr.local_binder_expr list ->
    Constrexpr.typeclass_constraint ->
    (bool * Constrexpr.constr_expr) option ->
    ?generalize:bool ->
    ?tac:unit Proofview.tactic  ->
    ?hook:(Globnames.global_reference -> unit) ->
    Vernacexpr.hint_info_expr ->
    Names.Id.t
end

module Vernacinterp :
sig
  type deprecation = bool

  type vernac_command = Genarg.raw_generic_argument list -> unit -> unit

  val vinterp_add : deprecation -> Vernacexpr.extend_name ->
    vernac_command -> unit

end

module Mltop :
sig
  val declare_cache_obj : (unit -> unit) -> string -> unit
  val add_known_plugin : (unit -> unit) -> string -> unit
  val add_known_module : string -> unit
  val module_is_known : string -> bool
end

module Topfmt :
sig
  val std_ft : Format.formatter ref
  val with_output_to : out_channel -> Format.formatter
  val get_margin : unit -> int option
end

module Vernacentries :
sig
  val dump_global : Libnames.reference Misctypes.or_by_notation -> unit
  val interp_redexp_hook : (Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr ->
                            Evd.evar_map * Redexpr.red_expr) Hook.t
  val command_focus : unit Proof.focus_kind
end

(************************************************************************)
(* End of modules from vernac/                                          *)
(************************************************************************)
