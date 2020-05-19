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

(** We provide two kind of functions:

  - one-go functions, that will register a constant in one go, suited
   for non-interactive definitions where the term is given.

  - two-phase [start/declare] functions which will create an
   interactive proof, allow its modification, and saving when
   complete.

  Internally, these functions mainly differ in that usually, the first
  case doesn't require setting up the tactic engine.

  Note that the API in this file is still in a state of flux, don't
  hesitate to contact the maintainers if you have any question.

  Additionally, this file does contain some low-level functions, marked
  as such; these functions are unstable and should not be used unless you
  already know what they are doing.

 *)

(** [Declare.Proof.t] Construction of constants using interactive proofs. *)
module Proof : sig

  type t

  (** XXX: These are internal and will go away from publis API once
     lemmas is merged here *)
  val get_proof : t -> Proof.t
  val get_proof_name : t -> Names.Id.t

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

   XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
type 'a proof_entry

(** XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
type proof_object

(** Used by the STM only to store info, should go away *)
val get_po_name : proof_object -> Id.t

val close_proof : opaque:opacity_flag -> keep_body_ucst_separate:bool -> Proof.t -> proof_object

(** Declaration of local constructions (Variable/Hypothesis/Local) *)

(** XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
type variable_declaration =
  | SectionLocalDef of Evd.side_effects proof_entry
  | SectionLocalAssum of { typ:types; impl:Glob_term.binding_kind; }

(** XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
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

   XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
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

type import_status = Locality.import_status = ImportDefaultBehavior | ImportNeedQualified

(** [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration

  internal specify if the constant has been created by the kernel or by the
  user, and in the former case, if its errors should be silent

  XXX: This is an internal, low-level API and could become scheduled
  for removal from the public API, use higher-level declare APIs
  instead *)
val declare_constant
  :  ?local:import_status
  -> name:Id.t
  -> kind:Decls.logical_kind
  -> Evd.side_effects constant_entry
  -> Constant.t

(** Declaration messages *)

(** XXX: Scheduled for removal from public API, do not use *)
val definition_message : Id.t -> unit
val assumption_message : Id.t -> unit
val fixpoint_message : int array option -> Id.t list -> unit

val check_exists : Id.t -> unit

(** {6 For legacy support, do not use}  *)

module Internal : sig

  type constant_obj

  val objConstant : constant_obj Libobject.Dyn.tag
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

(** Semantics of this function is a bit dubious, use with care *)
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

(** XXX: Temporarily re-exported for 3rd party code; don't use  *)
val build_constant_by_tactic :
  name:Names.Id.t ->
  ?opaque:opacity_flag ->
  uctx:UState.t ->
  sign:Environ.named_context_val ->
  poly:bool ->
  EConstr.types ->
  unit Proofview.tactic ->
  Evd.side_effects proof_entry * bool * UState.t
[@@ocaml.deprecated "This function is deprecated, used newer API in declare"]

val declare_universe_context : poly:bool -> Univ.ContextSet.t -> unit
[@@ocaml.deprecated "Use DeclareUctx.declare_universe_context"]

type locality = Locality.locality = Discharge | Global of import_status

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

(** XXX: This is an internal, low-level API and could become scheduled
    for removal from the public API, use higher-level declare APIs
    instead *)
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
   careful not to submit open terms or evar maps with stale,
   unresolved existentials *)
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

type lemma_possible_guards = int list list

val declare_mutually_recursive
  : opaque:bool
  -> scope:locality
  -> kind:Decls.logical_kind
  -> poly:bool
  -> uctx:UState.t
  -> udecl:UState.universe_decl
  -> ntns:Vernacexpr.decl_notation list
  -> rec_declaration:Constr.rec_declaration
  -> possible_indexes:lemma_possible_guards option
  -> ?restrict_ucontext:bool
  (** XXX: restrict_ucontext should be always true, this seems like a
     bug in obligations, so this parameter should go away *)
  -> Recthm.t list
  -> Names.GlobRef.t list

(** Prepare API, to be removed once we provide the corresponding 1-step API *)
val prepare_obligation
  :  name:Id.t
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

module Obls : sig

type 'a obligation_body = DefinedObl of 'a | TermObl of constr

module Obligation : sig
  type t = private
    { obl_name : Id.t
    ; obl_type : types
    ; obl_location : Evar_kinds.t Loc.located
    ; obl_body : pconstant obligation_body option
    ; obl_status : bool * Evar_kinds.obligation_definition_status
    ; obl_deps : Int.Set.t
    ; obl_tac : unit Proofview.tactic option }

  val set_type : typ:Constr.types -> t -> t
  val set_body : body:pconstant obligation_body -> t -> t
end

type obligations = {obls : Obligation.t array; remaining : int}
type fixpoint_kind = IsFixpoint of lident option list | IsCoFixpoint

(* Information about a single [Program {Definition,Lemma,..}] declaration *)
module ProgramDecl : sig
  type t = private
    { prg_name : Id.t
    ; prg_body : constr
    ; prg_type : constr
    ; prg_ctx : UState.t
    ; prg_univdecl : UState.universe_decl
    ; prg_obligations : obligations
    ; prg_deps : Id.t list
    ; prg_fixkind : fixpoint_kind option
    ; prg_implicits : Impargs.manual_implicits
    ; prg_notations : Vernacexpr.decl_notation list
    ; prg_poly : bool
    ; prg_scope : locality
    ; prg_kind : Decls.definition_object_kind
    ; prg_reduce : constr -> constr
    ; prg_hook : Hook.t option
    ; prg_opaque : bool }

  val make :
       ?opaque:bool
    -> ?hook:Hook.t
    -> Names.Id.t
    -> udecl:UState.universe_decl
    -> uctx:UState.t
    -> impargs:Impargs.manual_implicits
    -> poly:bool
    -> scope:locality
    -> kind:Decls.definition_object_kind
    -> Constr.constr option
    -> Constr.types
    -> Names.Id.t list
    -> fixpoint_kind option
    -> Vernacexpr.decl_notation list
    -> RetrieveObl.obligation_info
    -> (Constr.constr -> Constr.constr)
    -> t

  val set_uctx : uctx:UState.t -> t -> t
end

(** [declare_obligation] Save an obligation *)
val declare_obligation :
     ProgramDecl.t
  -> Obligation.t
  -> Constr.types
  -> Constr.types option
  -> Entries.universes_entry
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

(* This is a hack to make it possible for Obligations to craft a Qed
 * behind the scenes.  The fix_exn the Stm attaches to the Future proof
 * is not available here, so we provide a side channel to get it *)
val stm_get_fix_exn : (unit -> Exninfo.iexn -> Exninfo.iexn) ref

end

(** Creating high-level proofs with an associated constant *)
module Proof_ending : sig

  type t =
    | Regular
    | End_obligation of Obls.obligation_qed_info
    | End_derive of { f : Id.t; name : Id.t }
    | End_equations of
        { hook : Constant.t list -> Evd.evar_map -> unit
        ; i : Id.t
        ; types : (Environ.env * Evar.t * Evd.evar_info * EConstr.named_context * Evd.econstr) list
        ; sigma : Evd.evar_map
        }

end

module Info : sig
  type t
  val make
    :  ?hook: Hook.t
    (** Callback to be executed at the end of the proof *)
    -> ?proof_ending : Proof_ending.t
    (** Info for special constants *)
    -> ?scope : locality
    (** locality  *)
    -> ?kind:Decls.logical_kind
    (** Theorem, etc... *)
    -> ?compute_guard:lemma_possible_guards
    -> ?thms:Recthm.t list
    (** Both of those are internal, used by the upper layers but will
       become handled natively here in the future *)
    -> unit
    -> t

  (* Internal; used to initialize non-mutual proofs *)
  val add_first_thm :
    info:t
    -> name:Id.t
    -> typ:EConstr.t
    -> impargs:Impargs.manual_implicits
    -> t
end

val save_lemma_proved
  : proof:Proof.t
  -> info:Info.t
  -> opaque:opacity_flag
  -> idopt:Names.lident option
  -> unit

val save_lemma_admitted :
     proof:Proof.t
  -> info:Info.t
  -> unit

(** Special cases for delayed proofs, in this case we must provide the
   proof information so the proof won't be forced. *)
val save_lemma_admitted_delayed :
     proof:proof_object
  -> info:Info.t
  -> unit

val save_lemma_proved_delayed
  : proof:proof_object
  -> info:Info.t
  -> idopt:Names.lident option
  -> unit
