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
open Constr
open Entries

(** This module provides the official functions to declare new
   variables, parameters, constants and inductive types in the global
   environment. It also updates some accesory tables such as [Nametab]
   (name resolution), [Impargs], and [Notations]. *)

(** We provide two kind of fuctions:

  - one go functions, that will register a constant in one go, suited
   for non-interactive definitions where the term is given.

  - two-phase [start/declare] functions which will create an
   interactive proof, allow its modification, and saving when
   complete.

  Internally, these functions mainly differ in that usually, the first
  case doesn't require setting up the tactic engine.

 *)

(** [Declare.Proof.t] Construction of constants using interactive proofs. *)
module Proof : sig

  type t

  (** XXX: These are internal and will go away from publis API once
     lemmas is merged here *)
  val get_proof : t -> Proof.t
  val get_proof_name : t -> Names.Id.t

  (** XXX: These 3 are only used in lemmas  *)
  val get_used_variables : t -> Names.Id.Set.t option
  val get_universe_decl : t -> UState.universe_decl
  val get_initial_euctx : t -> UState.t

  val map_proof : (Proof.t -> Proof.t) -> t -> t
  val map_fold_proof : (Proof.t -> Proof.t * 'a) -> t -> t * 'a
  val map_fold_proof_endline : (unit Proofview.tactic -> Proof.t -> Proof.t * 'a) -> t -> t * 'a

  (** Sets the tactic to be used when a tactic line is closed with [...] *)
  val set_endline_tactic : Genarg.glob_generic_argument -> t -> t

  (** Sets the section variables assumed by the proof, returns its closure
   * (w.r.t. type dependencies and let-ins covered by it) *)
  val set_used_variables : t ->
    Names.Id.t list -> Constr.named_context * t

  val compact : t -> t

  (** Update the proofs global environment after a side-effecting command
      (e.g. a sublemma definition) has been run inside it. Assumes
      there_are_pending_proofs. *)
  val update_global_env : t -> t

  val get_open_goals : t -> int

end

type opacity_flag = Vernacexpr.opacity_flag = Opaque | Transparent

(** [start_proof ~name ~udecl ~poly sigma goals] starts a proof of
   name [name] with goals [goals] (a list of pairs of environment and
   conclusion); [poly] determines if the proof is universe
   polymorphic. The proof is started in the evar map [sigma] (which
   can typically contain universe constraints), and with universe
   bindings [udecl]. *)
val start_proof
  :  name:Names.Id.t
  -> udecl:UState.universe_decl
  -> poly:bool
  -> Evd.evar_map
  -> (Environ.env * EConstr.types) list
  -> Proof.t

(** Like [start_proof] except that there may be dependencies between
    initial goals. *)
val start_dependent_proof
  :  name:Names.Id.t
  -> udecl:UState.universe_decl
  -> poly:bool
  -> Proofview.telescope
  -> Proof.t

(** Proof entries represent a proof that has been finished, but still
   not registered with the kernel.

   XXX: Scheduled for removal from public API, don't rely on it *)
type 'a proof_entry = private {
  proof_entry_body   : 'a Entries.const_entry_body;
  (* List of section variables *)
  proof_entry_secctx : Id.Set.t option;
  (* State id on which the completion of type checking is reported *)
  proof_entry_feedback : Stateid.t option;
  proof_entry_type        : Constr.types option;
  proof_entry_universes   : Entries.universes_entry;
  proof_entry_opaque      : bool;
  proof_entry_inline_code : bool;
}

(** XXX: Scheduled for removal from public API, don't rely on it *)
type proof_object = private
  { name : Names.Id.t
  (** name of the proof *)
  ; entries : Evd.side_effects proof_entry list
  (** list of the proof terms (in a form suitable for definitions). *)
  ; uctx: UState.t
  (** universe state *)
  }

val close_proof : opaque:opacity_flag -> keep_body_ucst_separate:bool -> Proof.t -> proof_object

(** Declaration of local constructions (Variable/Hypothesis/Local) *)

(** XXX: Scheduled for removal from public API, don't rely on it *)
type variable_declaration =
  | SectionLocalDef of Evd.side_effects proof_entry
  | SectionLocalAssum of { typ:types; impl:Glob_term.binding_kind; }

(** XXX: Scheduled for removal from public API, don't rely on it *)
type 'a constant_entry =
  | DefinitionEntry of 'a proof_entry
  | ParameterEntry of parameter_entry
  | PrimitiveEntry of primitive_entry

val declare_variable
  :  name:variable
  -> kind:Decls.logical_kind
  -> variable_declaration
  -> unit

(** Declaration of global constructions
   i.e. Definition/Theorem/Axiom/Parameter/...

   XXX: Scheduled for removal from public API, use `DeclareDef` instead *)
val definition_entry
  : ?fix_exn:Future.fix_exn
  -> ?opaque:bool
  -> ?inline:bool
  -> ?feedback_id:Stateid.t
  -> ?section_vars:Id.Set.t
  -> ?types:types
  -> ?univs:Entries.universes_entry
  -> ?eff:Evd.side_effects
  -> ?univsbody:Univ.ContextSet.t
  (** Universe-constraints attached to the body-only, used in
     vio-delayed opaque constants and private poly universes *)
  -> constr
  -> Evd.side_effects proof_entry

type import_status = ImportDefaultBehavior | ImportNeedQualified

(** [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration

  internal specify if the constant has been created by the kernel or by the
  user, and in the former case, if its errors should be silent

  XXX: Scheduled for removal from public API, use `DeclareDef` instead *)
val declare_constant
  :  ?local:import_status
  -> name:Id.t
  -> kind:Decls.logical_kind
  -> Evd.side_effects constant_entry
  -> Constant.t

(** [inline_private_constants ~sideff ~uctx env ce] will inline the
   constants in [ce]'s body and return the body plus the updated
   [UState.t].

   XXX: Scheduled for removal from public API, don't rely on it *)
val inline_private_constants
  :  uctx:UState.t
  -> Environ.env
  -> Evd.side_effects proof_entry
  -> Constr.t * UState.t

(** Declaration messages *)

(** XXX: Scheduled for removal from public API, do not use *)
val definition_message : Id.t -> unit
val assumption_message : Id.t -> unit
val fixpoint_message : int array option -> Id.t list -> unit

val check_exists : Id.t -> unit

(** {6 For legacy support, do not use}  *)

module Internal : sig

  val map_entry_body : f:('a Entries.proof_output -> 'b Entries.proof_output) -> 'a proof_entry -> 'b proof_entry
  val map_entry_type : f:(Constr.t option -> Constr.t option) -> 'a proof_entry -> 'a proof_entry
  (* Overriding opacity is indeed really hacky *)
  val set_opacity : opaque:bool -> 'a proof_entry -> 'a proof_entry

  val shrink_entry : EConstr.named_context -> 'a proof_entry -> 'a proof_entry * Constr.constr list

  (* Liboject exports *)
  module Constant : sig
    type t
    val tag : t Libobject.Dyn.tag
    val kind : t -> Decls.logical_kind
  end

  val objVariable : unit Libobject.Dyn.tag

end

(* Intermediate step necessary to delegate the future.
 * Both access the current proof state. The former is supposed to be
 * chained with a computation that completed the proof *)
type closed_proof_output

(** Requires a complete proof. *)
val return_proof : Proof.t -> closed_proof_output

(** An incomplete proof is allowed (no error), and a warn is given if
   the proof is complete. *)
val return_partial_proof : Proof.t -> closed_proof_output
val close_future_proof : feedback_id:Stateid.t -> Proof.t -> closed_proof_output Future.computation -> proof_object

(** [by tac] applies tactic [tac] to the 1st subgoal of the current
    focused proof.
    Returns [false] if an unsafe tactic has been used. *)
val by : unit Proofview.tactic -> Proof.t -> Proof.t * bool

val build_by_tactic
  :  ?side_eff:bool
  -> Environ.env
  -> uctx:UState.t
  -> poly:bool
  -> typ:EConstr.types
  -> unit Proofview.tactic
  -> Constr.constr * Constr.types option * Entries.universes_entry * bool * UState.t

(** {6 Helpers to obtain proof state when in an interactive proof } *)

(** [get_goal_context n] returns the context of the [n]th subgoal of
   the current focused proof or raises a [UserError] if there is no
   focused proof or if there is no more subgoals *)

val get_goal_context : Proof.t -> int -> Evd.evar_map * Environ.env

(** [get_current_goal_context ()] works as [get_goal_context 1] *)
val get_current_goal_context : Proof.t -> Evd.evar_map * Environ.env

(** [get_current_context ()] returns the context of the
  current focused goal. If there is no focused goal but there
  is a proof in progress, it returns the corresponding evar_map.
  If there is no pending proof then it returns the current global
  environment and empty evar_map. *)
val get_current_context : Proof.t -> Evd.evar_map * Environ.env

(** Temporarily re-exported for 3rd party code; don't use  *)
val build_constant_by_tactic :
  name:Names.Id.t ->
  ?opaque:opacity_flag ->
  uctx:UState.t ->
  sign:Environ.named_context_val ->
  poly:bool ->
  EConstr.types ->
  unit Proofview.tactic ->
  Evd.side_effects proof_entry * bool * UState.t

val declare_universe_context : poly:bool -> Univ.ContextSet.t -> unit
[@@ocaml.deprecated "Use DeclareUctx.declare_universe_context"]

type locality = Discharge | Global of import_status

(** Declaration hooks *)
module Hook : sig
  type t

  (** Hooks allow users of the API to perform arbitrary actions at
     proof/definition saving time. For example, to register a constant
     as a Coercion, perform some cleanup, update the search database,
     etc...  *)
  module S : sig
    type t =
      { uctx : UState.t
      (** [ustate]: universe constraints obtained when the term was closed *)
      ; obls : (Id.t * Constr.t) list
      (** [(n1,t1),...(nm,tm)]: association list between obligation
          name and the corresponding defined term (might be a constant,
          but also an arbitrary term in the Expand case of obligations) *)
      ; scope : locality
      (** [scope]: Locality of the original declaration *)
      ; dref : GlobRef.t
      (** [dref]: identifier of the original declaration *)
      }
  end

  val make : (S.t -> unit) -> t
  val call : ?hook:t -> S.t -> unit
end

(** Declare an interactively-defined constant *)
val declare_entry
  :  name:Id.t
  -> scope:locality
  -> kind:Decls.logical_kind
  -> ?hook:Hook.t
  -> ?obls:(Id.t * Constr.t) list
  -> impargs:Impargs.manual_implicits
  -> uctx:UState.t
  -> Evd.side_effects proof_entry
  -> GlobRef.t

(** Declares a non-interactive constant; [body] and [types] will be
   normalized w.r.t. the passed [evar_map] [sigma]. Universes should
   be handled properly, including minimization and restriction. Note
   that [sigma] is checked for unresolved evars, thus you should be
   careful not to submit open terms *)
val declare_definition
  :  name:Id.t
  -> scope:locality
  -> kind:Decls.logical_kind
  -> opaque:bool
  -> impargs:Impargs.manual_implicits
  -> udecl:UState.universe_decl
  -> ?hook:Hook.t
  -> ?obls:(Id.t * Constr.t) list
  -> poly:bool
  -> ?inline:bool
  -> types:EConstr.t option
  -> body:EConstr.t
  -> ?fix_exn:(Exninfo.iexn -> Exninfo.iexn)
  -> Evd.evar_map
  -> GlobRef.t

val declare_assumption
  :  ?fix_exn:(Exninfo.iexn -> Exninfo.iexn)
  -> name:Id.t
  -> scope:locality
  -> hook:Hook.t option
  -> impargs:Impargs.manual_implicits
  -> uctx:UState.t
  -> Entries.parameter_entry
  -> GlobRef.t

module Recthm : sig
  type t =
    { name : Id.t
    (** Name of theorem *)
    ; typ : Constr.t
    (** Type of theorem  *)
    ; args : Name.t list
    (** Names to pre-introduce  *)
    ; impargs : Impargs.manual_implicits
    (** Explicitily declared implicit arguments  *)
    }
end

val declare_mutually_recursive
  : opaque:bool
  -> scope:locality
  -> kind:Decls.logical_kind
  -> poly:bool
  -> uctx:UState.t
  -> udecl:UState.universe_decl
  -> ntns:Vernacexpr.decl_notation list
  -> rec_declaration:Constr.rec_declaration
  -> possible_indexes:int list list option
  -> ?restrict_ucontext:bool
  (** XXX: restrict_ucontext should be always true, this seems like a
     bug in obligations, so this parameter should go away *)
  -> Recthm.t list
  -> Names.GlobRef.t list

val prepare_obligation
  :  ?opaque:bool
  -> ?inline:bool
  -> name:Id.t
  -> poly:bool
  -> udecl:UState.universe_decl
  -> types:EConstr.t option
  -> body:EConstr.t
  -> Evd.evar_map
  -> Constr.constr * Constr.types * UState.t * RetrieveObl.obligation_info

val prepare_parameter
  : poly:bool
  -> udecl:UState.universe_decl
  -> types:EConstr.types
  -> Evd.evar_map
  -> Evd.evar_map * Entries.parameter_entry

(* Compat: will remove *)
exception AlreadyDeclared of (string option * Names.Id.t)
