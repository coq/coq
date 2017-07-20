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

(************************************************************************)
(* Modules from proofs/                                                 *)
(************************************************************************)

module Miscprint :
sig
  val pr_or_and_intro_pattern :
    ('a -> Pp.std_ppcmds) -> 'a Misctypes.or_and_intro_pattern_expr -> Pp.std_ppcmds
  val pr_intro_pattern_naming : Misctypes.intro_pattern_naming_expr -> Pp.std_ppcmds
  val pr_intro_pattern :
    ('a -> Pp.std_ppcmds) -> 'a Misctypes.intro_pattern_expr Loc.located -> Pp.std_ppcmds
  val pr_bindings :
    ('a -> Pp.std_ppcmds) ->
    ('a -> Pp.std_ppcmds) -> 'a Misctypes.bindings -> Pp.std_ppcmds
  val pr_bindings_no_with :
    ('a -> Pp.std_ppcmds) ->
    ('a -> Pp.std_ppcmds) -> 'a Misctypes.bindings -> Pp.std_ppcmds
  val pr_with_bindings :
    ('a -> Pp.std_ppcmds) ->
    ('a -> Pp.std_ppcmds) -> 'a * 'a Misctypes.bindings -> Pp.std_ppcmds
end

(* All items in the Goal modules are deprecated. *)
module Goal :
sig
  type goal = Evar.t

  val pr_goal : goal -> Pp.std_ppcmds

  module V82 :
  sig
    val new_goal_with : Evd.evar_map -> goal -> Context.Named.t -> goal Evd.sigma

    val nf_hyps : Evd.evar_map -> goal -> Environ.named_context_val

    val env : Evd.evar_map -> goal -> Environ.env

    val concl : Evd.evar_map -> goal -> EConstr.constr

    val mk_goal : Evd.evar_map ->
                  Environ.named_context_val ->
                  EConstr.constr ->
                  Evd.Store.t ->
                  goal * EConstr.constr * Evd.evar_map

    val extra : Evd.evar_map -> goal -> Evd.Store.t

    val partial_solution_to : Evd.evar_map -> goal -> goal -> EConstr.constr -> Evd.evar_map

    val partial_solution : Evd.evar_map -> goal -> EConstr.constr -> Evd.evar_map

    val hyps : Evd.evar_map -> goal -> Environ.named_context_val

    val abstract_type : Evd.evar_map -> goal -> EConstr.types
  end
end

module Evar_refiner :
sig
  val w_refine : Evar.t * Evd.evar_info ->
                 Pretyping.glob_constr_ltac_closure -> Evd.evar_map -> Evd.evar_map
end


module Proof_type :
sig
  type prim_rule =
    | Cut of bool * bool * Names.Id.t * Term.types
    | Refine of Constr.t

  type tactic = Goal.goal Evd.sigma -> Goal.goal list Evd.sigma
end

module Logic :
sig
  type refiner_error =
  | BadType of Constr.t * Constr.t * Constr.t
  | UnresolvedBindings of Names.Name.t list
  | CannotApply of Constr.t * Constr.t
  | NotWellTyped of Constr.t
  | NonLinearProof of Constr.t
  | MetaInType of EConstr.constr
  | IntroNeedsProduct
  | DoesNotOccurIn of Constr.t * Names.Id.t
  | NoSuchHyp of Names.Id.t
  exception RefinerError of refiner_error
  val catchable_exception : exn -> bool
end

module Refine :
sig
  val refine : typecheck:bool -> (Evd.evar_map -> Evd.evar_map * EConstr.t) -> unit Proofview.tactic
  val solve_constraints : unit Proofview.tactic
end

module Proof :
sig
  type proof
  type 'a focus_kind

  val run_tactic : Environ.env ->
                   unit Proofview.tactic -> proof -> proof * (bool * Proofview_monad.Info.tree)
  val unshelve : proof -> proof
  val maximal_unfocus : 'a focus_kind -> proof -> proof
  val pr_proof : proof -> Pp.std_ppcmds
  module V82 :
  sig
    val grab_evars : proof -> proof

    val subgoals : proof -> Goal.goal list Evd.sigma
  end
end

module Proof_bullet :
sig
  val get_default_goal_selector : unit -> Vernacexpr.goal_selector
end

module Proof_global :
sig
  type proof_mode = {
      name : string;
      set : unit -> unit ;
      reset : unit -> unit
    }
  type proof_universes = UState.t * Universes.universe_binders option
  type proof_object = {
    id : Names.Id.t;
    entries : Safe_typing.private_constants Entries.definition_entry list;
    persistence : Decl_kinds.goal_kind;
    universes: proof_universes;
  }

  type proof_ending =
  | Admitted of Names.Id.t * Decl_kinds.goal_kind * Entries.parameter_entry *
                  proof_universes
  | Proved of Vernacexpr.opacity_flag *
              Vernacexpr.lident option *
              proof_object

  type proof_terminator
  type lemma_possible_guards
  type universe_binders
  type closed_proof = proof_object * proof_terminator

  val make_terminator : (proof_ending -> unit) -> proof_terminator
  val start_dependent_proof :
    Names.Id.t -> ?pl:universe_binders -> Decl_kinds.goal_kind ->
    Proofview.telescope -> proof_terminator -> unit
  val with_current_proof :
    (unit Proofview.tactic -> Proof.proof -> Proof.proof * 'a) -> 'a
  val simple_with_current_proof :
    (unit Proofview.tactic -> Proof.proof -> Proof.proof) -> unit
  val compact_the_proof : unit -> unit
  val register_proof_mode : proof_mode -> unit

  exception NoCurrentProof
  val give_me_the_proof : unit -> Proof.proof
  (** @raise NoCurrentProof when outside proof mode. *)

  val discard_all : unit -> unit
  val discard_current : unit -> unit
  val get_current_proof_name : unit -> Names.Id.t
end

module Redexpr :
sig
  type red_expr =
    (EConstr.constr, Names.evaluable_global_reference, Pattern.constr_pattern) Genredexpr.red_expr_gen
  val reduction_of_red_expr :
    Environ.env -> red_expr -> Reductionops.e_reduction_function * Constr.cast_kind
  val declare_reduction : string -> Reductionops.reduction_function -> unit
end

module Refiner :
sig
  val project : 'a Evd.sigma -> Evd.evar_map

  val unpackage : 'a Evd.sigma -> Evd.evar_map ref * 'a

  val repackage : Evd.evar_map ref -> 'a -> 'a Evd.sigma

  val tclSHOWHYPS : Proof_type.tactic -> Proof_type.tactic
  exception FailError of int * Pp.std_ppcmds Lazy.t

  val tclEVARS : Evd.evar_map -> Proof_type.tactic
  val tclMAP : ('a -> Proof_type.tactic) -> 'a list -> Proof_type.tactic
  val tclREPEAT : Proof_type.tactic -> Proof_type.tactic
  val tclORELSE        : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
  val tclFAIL : int -> Pp.std_ppcmds -> Proof_type.tactic
  val tclIDTAC : Proof_type.tactic
  val tclTHEN : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
  val tclTHENLIST : Proof_type.tactic list -> Proof_type.tactic
  val tclTRY : Proof_type.tactic -> Proof_type.tactic
  val tclAT_LEAST_ONCE : Proof_type.tactic -> Proof_type.tactic
end

module Tacmach :
sig

  type tactic = Proof_type.tactic

  type 'a sigma = 'a Evd.sigma
  [@@ocaml.deprecated "alias of API.Evd.sigma"]

  val re_sig : 'a -> Evd.evar_map -> 'a Evd.sigma

  val pf_reduction_of_red_expr : Goal.goal Evd.sigma -> Redexpr.red_expr -> EConstr.constr -> Evd.evar_map * EConstr.constr

  val pf_unsafe_type_of : Goal.goal Evd.sigma -> EConstr.constr -> EConstr.types

  val pf_get_new_id  : Names.Id.t -> Goal.goal Evd.sigma -> Names.Id.t

  val pf_env : Goal.goal Evd.sigma -> Environ.env

  val pf_concl : Goal.goal Evd.sigma -> EConstr.types

  val pf_apply : (Environ.env -> Evd.evar_map -> 'a) -> Goal.goal Evd.sigma -> 'a

  val pf_get_hyp            : Goal.goal Evd.sigma -> Names.Id.t -> EConstr.named_declaration
  val pf_get_hyp_typ        : Goal.goal Evd.sigma -> Names.Id.t -> EConstr.types
  val project : Goal.goal Evd.sigma -> Evd.evar_map
  val refine : EConstr.constr -> Proof_type.tactic
  val refine_no_check : EConstr.constr -> Proof_type.tactic
  val pf_type_of : Goal.goal Evd.sigma -> EConstr.constr -> Evd.evar_map * EConstr.types

  val pf_hyps : Goal.goal Evd.sigma -> EConstr.named_context

  val pf_ids_of_hyps : Goal.goal Evd.sigma -> Names.Id.t list

  val pf_reduce_to_atomic_ind : Goal.goal Evd.sigma -> EConstr.types -> (Names.inductive * EConstr.EInstance.t) * EConstr.types

  val pf_reduce_to_quantified_ind : Goal.goal Evd.sigma -> EConstr.types -> (Names.inductive * EConstr.EInstance.t) * EConstr.types

  val pf_eapply : (Environ.env -> Evd.evar_map -> 'a -> Evd.evar_map * 'b) ->
                  Evar.t Evd.sigma -> 'a -> Evar.t Evd.sigma * 'b

  val pf_unfoldn : (Locus.occurrences * Names.evaluable_global_reference) list
                   -> Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr

  val pf_reduce : (Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr) -> Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr

  val pf_conv_x : Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr -> bool

  val pf_is_matching : Goal.goal Evd.sigma -> Pattern.constr_pattern -> EConstr.constr -> bool

  val pf_hyps_types : Goal.goal Evd.sigma -> (Names.Id.t * EConstr.types) list

  val pr_gls    : Goal.goal Evd.sigma -> Pp.std_ppcmds

  val pf_nf_betaiota : Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr

  val pf_last_hyp : Goal.goal Evd.sigma -> EConstr.named_declaration

  val pf_nth_hyp_id : Goal.goal Evd.sigma -> int -> Names.Id.t

  val sig_it : 'a Evd.sigma -> 'a

  module New :
  sig
    val pf_apply : (Environ.env -> Evd.evar_map -> 'a) -> 'b Proofview.Goal.t -> 'a
    val project : 'a Proofview.Goal.t -> Evd.evar_map
    val pf_unsafe_type_of : 'a Proofview.Goal.t -> EConstr.constr -> EConstr.types
    val of_old : (Goal.goal Evd.sigma -> 'a) -> [ `NF ] Proofview.Goal.t -> 'a

    val pf_env : 'a Proofview.Goal.t -> Environ.env
    val pf_ids_of_hyps : 'a Proofview.Goal.t -> Names.Id.t list
    val pf_concl : 'a Proofview.Goal.t -> EConstr.types
    val pf_get_new_id  : Names.Id.t -> 'a Proofview.Goal.t -> Names.Id.t
    val pf_get_hyp_typ : Names.Id.t -> 'a Proofview.Goal.t -> EConstr.types
    val pf_get_type_of : 'a Proofview.Goal.t -> EConstr.constr -> EConstr.types
    val pf_global : Names.Id.t -> 'a Proofview.Goal.t -> Globnames.global_reference
    val pf_hyps_types : 'a Proofview.Goal.t -> (Names.Id.t * EConstr.types) list
  end
end

module Pfedit :
sig
  val solve_by_implicit_tactic : unit -> Pretyping.inference_hook option
  val refine_by_tactic : Environ.env -> Evd.evar_map -> EConstr.types -> unit Proofview.tactic ->
                         Constr.t * Evd.evar_map
  val declare_implicit_tactic : unit Proofview.tactic -> unit
  val clear_implicit_tactic : unit -> unit
  val by : unit Proofview.tactic -> bool
  val solve : ?with_end_tac:unit Proofview.tactic ->
      Vernacexpr.goal_selector -> int option -> unit Proofview.tactic ->
      Proof.proof -> Proof.proof * bool
  val cook_proof :
    unit -> (Names.Id.t * (Safe_typing.private_constants Entries.definition_entry * Proof_global.proof_universes * Decl_kinds.goal_kind))

  val get_current_context : unit -> Evd.evar_map * Environ.env

  (* Deprecated *)
  val delete_current_proof : unit -> unit
  [@@ocaml.deprecated "use Proof_global.discard_current"]

  val get_current_proof_name : unit -> Names.Id.t
  [@@ocaml.deprecated "use Proof_global.get_current_proof_name"]

end

module Clenv :
sig

  type hole = {
    hole_evar : EConstr.constr;
    hole_type : EConstr.types;
    hole_deps  : bool;
    hole_name : Names.Name.t;
  }

  type clause = {
    cl_holes : hole list;
    cl_concl : EConstr.types;
  }

  val make_evar_clause : Environ.env -> Evd.evar_map -> ?len:int -> EConstr.types ->
                         (Evd.evar_map * clause)
  val solve_evar_clause : Environ.env -> Evd.evar_map -> bool -> clause -> EConstr.constr Misctypes.bindings ->
                          Evd.evar_map
  type clausenv
  val pr_clenv : clausenv -> Pp.std_ppcmds
end

(************************************************************************)
(* End of modules from proofs/                                          *)
(************************************************************************)
