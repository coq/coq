(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** This module provides the functions to declare new
   variables, parameters, constants and inductive types in the global
   environment. It also updates some accesory tables such as [Nametab]
   (name resolution), [Impargs], and [Notations]. *)

(** We provide three main entry points:

  - one-go functions, that will register a constant in one go, suited
   for non-interactive definitions where the term is given.

  - two-phase [start/save] functions which will create an
   interactive proof, allow its modification using tactics, and saving
   when complete.

  - program mode API, that allow to declare a constant with holes, to
   be fullfilled later.

  Note that the API in this file is still in a state of flux, don't
  hesitate to contact the maintainers if you have any question.

  Additionally, this file does contain some low-level functions, marked
  as such; these functions are unstable and should not be used unless you
  already know what they are doing.

 *)

(** Declaration hooks, to be run when a constant is saved. Use with
   care, as imperative effects may become not supported in the
   future. *)
module Hook : sig
  type t

  (** Hooks allow users of the API to perform arbitrary actions at
     proof/definition saving time. For example, to register a constant
     as a Coercion, perform some cleanup, update the search database,
     etc... *)
  module S : sig
    type t =
      { uctx : UState.t
      (** [ustate]: universe constraints obtained when the term was closed *)
      ; obls : (Id.t * Constr.t) list
      (** [(n1,t1),...(nm,tm)]: association list between obligation
          name and the corresponding defined term (might be a constant,
          but also an arbitrary term in the Expand case of obligations) *)
      ; scope : Locality.locality
      (** [scope]: Locality of the original declaration *)
      ; dref : GlobRef.t
      (** [dref]: identifier of the original declaration *)
      }
  end

  val make : (S.t -> unit) -> t
  val call : ?hook:t -> S.t -> unit
end

(** {2 One-go, non-interactive declaration API } *)

(** Information for a single top-level named constant *)
module CInfo : sig
  type 'constr t

  val make :
    name : Id.t
    -> typ:'constr
    -> ?args:Name.t list
    -> ?impargs:Impargs.manual_implicits
    -> unit
    -> 'constr t

  (* Eventually we would like to remove the constr parameter *)
  val to_constr : Evd.evar_map -> EConstr.t t -> Constr.t t

  val get_typ : 'constr t -> 'constr
  (* To be removed once obligations are merged here *)
  val get_name : 'constr t -> Id.t

end

(** Information for a declaration, interactive or not, includes
   parameters shared by mutual constants *)
module Info : sig

  type t

  (** Note that [opaque] doesn't appear here as it is not known at the
     start of the proof in the interactive case. *)
  val make
    : ?poly:bool
    -> ?inline : bool
    -> ?kind : Decls.logical_kind
    (** Theorem, etc... *)
    -> ?udecl : UState.universe_decl
    -> ?scope : Locality.locality
    (** locality  *)
    -> ?hook : Hook.t
    (** Callback to be executed after saving the constant *)
    -> unit
    -> t

end

(** Declares a non-interactive constant; [body] and [types] will be
   normalized w.r.t. the passed [evar_map] [sigma]. Universes should
   be handled properly, including minimization and restriction. Note
   that [sigma] is checked for unresolved evars, thus you should be
   careful not to submit open terms or evar maps with stale,
   unresolved existentials *)
val declare_definition
  :  info:Info.t
  -> cinfo:EConstr.t option CInfo.t
  -> opaque:bool
  -> body:EConstr.t
  -> Evd.evar_map
  -> GlobRef.t

val declare_assumption
  :  name:Id.t
  -> scope:Locality.locality
  -> hook:Hook.t option
  -> impargs:Impargs.manual_implicits
  -> uctx:UState.t
  -> Entries.parameter_entry
  -> GlobRef.t

type lemma_possible_guards = int list list

val declare_mutually_recursive
  : info:Info.t
  -> cinfo: Constr.t CInfo.t list
  -> opaque:bool
  -> ntns:Vernacexpr.decl_notation list
  -> uctx:UState.t
  -> rec_declaration:Constr.rec_declaration
  -> possible_indexes:lemma_possible_guards option
  -> Names.GlobRef.t list

(** {2 Declaration of interactive constants }  *)

(** Resolution status of a program *)
type progress =
  | Remain of int  (** n obligations remaining *)
  | Dependent  (** Dependent on other definitions *)
  | Defined of GlobRef.t  (** Defined as id *)

type obligation_resolver =
     Id.t option
  -> Int.Set.t
  -> unit Proofview.tactic option
  -> progress

type obligation_qed_info = {name : Id.t; num : int; auto : obligation_resolver}

(** Creating high-level proofs with an associated constant *)
module Proof_ending : sig

  type t =
    | Regular
    | End_obligation of obligation_qed_info
    | End_derive of { f : Id.t; name : Id.t }
    | End_equations of
        { hook : Constant.t list -> Evd.evar_map -> unit
        ; i : Id.t
        ; types : (Environ.env * Evar.t * Evd.evar_info * EConstr.named_context * Evd.econstr) list
        ; sigma : Evd.evar_map
        }

end

(** [Declare.Proof.t] Construction of constants using interactive proofs. *)
module Proof : sig

  type t

  (** [start_proof ~info ~cinfo sigma] starts a proof of [cinfo].
      The proof is started in the evar map [sigma] (which
      can typically contain universe constraints) *)
  val start
    :  info:Info.t
    -> cinfo:EConstr.t CInfo.t
    -> ?proof_ending:Proof_ending.t
    -> Evd.evar_map
    -> t

  (** Like [start] except that there may be dependencies between initial goals. *)
  val start_dependent
    : info:Info.t
    -> name:Id.t
    -> Proofview.telescope
    -> proof_ending:Proof_ending.t
    -> t

  (** Pretty much internal, used by the Lemmavernaculars *)
  val start_with_initialization
    :  info:Info.t
    -> cinfo:Constr.t CInfo.t
    -> Evd.evar_map
    -> t

  type mutual_info = (bool * lemma_possible_guards * Constr.t option list option)

  (** Pretty much internal, used by mutual Lemma / Fixpoint vernaculars *)
  val start_mutual_with_initialization
    :  info:Info.t
    -> cinfo:Constr.t CInfo.t list
    -> mutual_info:mutual_info
    -> Evd.evar_map
    -> int list option
    -> t

  (** Qed a proof  *)
  val save
    : proof:t
    -> opaque:Vernacexpr.opacity_flag
    -> idopt:Names.lident option
    -> unit

  (** Admit a proof *)
  val save_admitted : proof:t -> unit

  (** [by tac] applies tactic [tac] to the 1st subgoal of the current
      focused proof.
      Returns [false] if an unsafe tactic has been used. *)
  val by : unit Proofview.tactic -> t -> t * bool

  (** Operations on ongoing proofs *)
  val get : t -> Proof.t
  val get_name : t -> Names.Id.t

  val fold : f:(Proof.t -> 'a) -> t -> 'a
  val map : f:(Proof.t -> Proof.t) -> t -> t
  val map_fold : f:(Proof.t -> Proof.t * 'a) -> t -> t * 'a
  val map_fold_endline : f:(unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> t -> t * 'a

  (** Sets the tactic to be used when a tactic line is closed with [...] *)
  val set_endline_tactic : Genarg.glob_generic_argument -> t -> t

  (** Sets the section variables assumed by the proof, returns its closure
   * (w.r.t. type dependencies and let-ins covered by it) *)
  val set_used_variables : t -> Names.Id.t list -> Constr.named_context * t

  val compact : t -> t

  (** Update the proofs global environment after a side-effecting command
      (e.g. a sublemma definition) has been run inside it. Assumes
      there_are_pending_proofs. *)
  val update_global_env : t -> t

  val get_open_goals : t -> int

  (** Helpers to obtain proof state when in an interactive proof *)

  (** [get_goal_context n] returns the context of the [n]th subgoal of
      the current focused proof or raises a [UserError] if there is no
      focused proof or if there is no more subgoals *)

  val get_goal_context : t -> int -> Evd.evar_map * Environ.env

  (** [get_current_goal_context ()] works as [get_goal_context 1] *)
  val get_current_goal_context : t -> Evd.evar_map * Environ.env

  (** [get_current_context ()] returns the context of the
      current focused goal. If there is no focused goal but there
      is a proof in progress, it returns the corresponding evar_map.
      If there is no pending proof then it returns the current global
      environment and empty evar_map. *)
  val get_current_context : t -> Evd.evar_map * Environ.env

  (* Internal, don't use *)
  module Proof_info : sig
    type t
    (* Make a dummy value, used in the stm *)
    val default : unit -> t
  end
  val info : t -> Proof_info.t
end

(** {2 low-level, internla API, avoid using unless you have special needs } *)

(** Proof entries represent a proof that has been finished, but still
   not registered with the kernel.

   XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
type 'a proof_entry

val definition_entry
  :  ?opaque:bool
  -> ?inline:bool
  -> ?types:Constr.types
  -> ?univs:Entries.universes_entry
  -> Constr.constr
  -> Evd.side_effects proof_entry

(** XXX: This is an internal, low-level API and could become scheduled
    for removal from the public API, use higher-level declare APIs
    instead *)
val declare_entry
  :  name:Id.t
  -> scope:Locality.locality
  -> kind:Decls.logical_kind
  -> ?hook:Hook.t
  -> impargs:Impargs.manual_implicits
  -> uctx:UState.t
  -> Evd.side_effects proof_entry
  -> GlobRef.t

(** Declaration of local constructions (Variable/Hypothesis/Local) *)
val declare_variable
  :  name:variable
  -> kind:Decls.logical_kind
  -> typ:Constr.types
  -> impl:Glob_term.binding_kind
  -> unit

(** Declaration of global constructions
   i.e. Definition/Theorem/Axiom/Parameter/...

   XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
type 'a constant_entry =
  | DefinitionEntry of 'a proof_entry
  | ParameterEntry of Entries.parameter_entry
  | PrimitiveEntry of Entries.primitive_entry

val prepare_parameter
  : poly:bool
  -> udecl:UState.universe_decl
  -> types:EConstr.types
  -> Evd.evar_map
  -> Evd.evar_map * Entries.parameter_entry

(** [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration

  XXX: This is an internal, low-level API and could become scheduled
  for removal from the public API, use higher-level declare APIs
  instead *)
val declare_constant
  :  ?local:Locality.import_status
  -> name:Id.t
  -> kind:Decls.logical_kind
  -> Evd.side_effects constant_entry
  -> Constant.t

(** {2 Proof delay API, warning, internal, not stable *)

(* Intermediate step necessary to delegate the future.
 * Both access the current proof state. The former is supposed to be
 * chained with a computation that completed the proof *)
type closed_proof_output

(** Requires a complete proof. *)
val return_proof : Proof.t -> closed_proof_output

(** An incomplete proof is allowed (no error), and a warn is given if
   the proof is complete. *)
val return_partial_proof : Proof.t -> closed_proof_output

(** XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
type proof_object

val close_proof : opaque:Vernacexpr.opacity_flag -> keep_body_ucst_separate:bool -> Proof.t -> proof_object
val close_future_proof : feedback_id:Stateid.t -> Proof.t -> closed_proof_output Future.computation -> proof_object

(** Special cases for delayed proofs, in this case we must provide the
   proof information so the proof won't be forced. *)
val save_lemma_admitted_delayed :
     proof:proof_object
  -> pinfo:Proof.Proof_info.t
  -> unit

val save_lemma_proved_delayed
  : proof:proof_object
  -> pinfo:Proof.Proof_info.t
  -> idopt:Names.lident option
  -> unit

(** Used by the STM only to store info, should go away *)
val get_po_name : proof_object -> Id.t

(** Declaration messages, for internal use *)

(** XXX: Scheduled for removal from public API, do not use *)
val definition_message : Id.t -> unit
val assumption_message : Id.t -> unit
val fixpoint_message : int array option -> Id.t list -> unit

val check_exists : Id.t -> unit

(** Semantics of this function is a bit dubious, use with care *)
val build_by_tactic
  :  ?side_eff:bool
  -> Environ.env
  -> uctx:UState.t
  -> poly:bool
  -> typ:EConstr.types
  -> unit Proofview.tactic
  -> Constr.constr * Constr.types option * Entries.universes_entry * bool * UState.t

(** {2 Program mode API} *)

(** Prepare API, to be removed once we provide the corresponding 1-step API *)
val prepare_obligation
  :  name:Id.t
  -> types:EConstr.t option
  -> body:EConstr.t
  -> Evd.evar_map
  -> Constr.constr * Constr.types * UState.t * RetrieveObl.obligation_info

module Obls : sig

type 'a obligation_body = DefinedObl of 'a | TermObl of Constr.constr

module Obligation : sig
  type t = private
    { obl_name : Id.t
    ; obl_type : Constr.types
    ; obl_location : Evar_kinds.t Loc.located
    ; obl_body : Constr.pconstant obligation_body option
    ; obl_status : bool * Evar_kinds.obligation_definition_status
    ; obl_deps : Int.Set.t
    ; obl_tac : unit Proofview.tactic option }

  val set_type : typ:Constr.types -> t -> t
  val set_body : body:Constr.pconstant obligation_body -> t -> t
end

type obligations = {obls : Obligation.t array; remaining : int}
type fixpoint_kind = IsFixpoint of lident option list | IsCoFixpoint

(* Information about a single [Program {Definition,Lemma,..}] declaration *)
module ProgramDecl : sig
  type t

  val make :
       info:Info.t
    -> cinfo:Constr.types CInfo.t
    -> opaque:bool
    -> ntns:Vernacexpr.decl_notation list
    -> reduce:(Constr.constr -> Constr.constr)
    -> deps:Names.Id.t list
    -> uctx:UState.t
    -> body:Constr.constr option
    -> fixpoint_kind:fixpoint_kind option
    -> RetrieveObl.obligation_info
    -> t

  val show : t -> Pp.t

  (* This is internal, only here as obligations get merged into the
     regular declaration path *)
  module Internal : sig
    val get_poly : t -> bool
    val get_name : t -> Id.t
    val get_uctx : t -> UState.t
    val set_uctx : uctx:UState.t -> t -> t
    val get_obligations : t -> obligations
  end
end

(** [declare_obligation prg obl ~uctx ~types ~body] Save an obligation
   [obl] for program definition [prg] *)
val declare_obligation :
     ProgramDecl.t
  -> Obligation.t
  -> uctx:UState.t
  -> types:Constr.types option
  -> body:Constr.types
  -> bool * Obligation.t

module State : sig

  val num_pending : unit -> int
  val first_pending : unit -> ProgramDecl.t option

  (** Returns [Error duplicate_list] if not a single program is open *)
  val get_unique_open_prog :
    Id.t option -> (ProgramDecl.t, Id.t list) result

  (** Add a new obligation *)
  val add : Id.t -> ProgramDecl.t -> unit

  val fold : f:(Id.t -> ProgramDecl.t -> 'a -> 'a) -> init:'a -> 'a

  val all : unit -> ProgramDecl.t list

  val find : Id.t -> ProgramDecl.t option

  (* Internal *)
  type t
  val prg_tag : t Summary.Dyn.tag
end

val declare_definition : ProgramDecl.t -> Names.GlobRef.t

(** [update_obls prg obls n progress] What does this do? *)
val update_obls :
  ProgramDecl.t -> Obligation.t array -> int -> progress

(** Check obligations are properly solved before closing the
   [what_for] section / module *)
val check_solved_obligations : what_for:Pp.t -> unit

(** { 2 Util }  *)

val obl_substitution :
     bool
  -> Obligation.t array
  -> Int.Set.t
  -> (Id.t * (Constr.types * Constr.types)) list

val dependencies : Obligation.t array -> int -> Int.Set.t

end

(** {6 For internal support, do not use}  *)

module Internal : sig

  type constant_obj

  val objConstant : constant_obj Libobject.Dyn.tag
  val objVariable : unit Libobject.Dyn.tag

end
