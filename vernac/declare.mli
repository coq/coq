(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
   environment. It also updates some accessory tables such as [Nametab]
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
  type 'a g

  type t = unit g

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
      ; scope : Locality.definition_scope
      (** [scope]: Locality of the original declaration *)
      ; dref : GlobRef.t
      (** [dref]: identifier of the original declaration *)
      }
  end

  val make_g : (S.t -> 'a -> 'a) -> 'a g
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

  (* Used only in Vernacentries, may disappear from public API *)
  val to_constr : Evd.evar_map -> EConstr.t t -> Constr.t t

  (* Used only in RecLemmas, may disappear from public API *)
  val get_typ : 'constr t -> 'constr

end

(** Information for a declaration, interactive or not, includes
   parameters shared by mutual constants *)
module Info : sig

  type t

  (** Note that [opaque] doesn't appear here as it is not known at the
     start of the proof in the interactive case. *)
  val make
    : ?loc:Loc.t
    -> ?poly:bool
    -> ?inline : bool
    -> ?kind : Decls.logical_kind
    (** Theorem, etc... *)
    -> ?udecl : UState.universe_decl
    -> ?scope : Locality.definition_scope
    (** locality  *)
    -> ?clearbody:bool
    -> ?hook : Hook.t
    (** Callback to be executed after saving the constant *)
    -> ?typing_flags:Declarations.typing_flags
    -> ?user_warns : Globnames.extended_global_reference UserWarn.with_qf
    -> ?ntns : Metasyntax.notation_interpretation_decl list
    -> unit
    -> t

end

(** Declares a non-interactive constant; [body] and [types] will be
   normalized w.r.t. the passed [evar_map] [sigma]. Universes should
   be handled properly, including minimization and restriction. Note
   that [sigma] is checked for unresolved evars, thus you should be
   careful not to submit open terms *)
val declare_definition
  :  info:Info.t
  -> cinfo:EConstr.t option CInfo.t
  -> opaque:bool
  -> body:EConstr.t
  -> ?using:Vernacexpr.section_subset_expr
  -> Evd.evar_map
  -> GlobRef.t

val declare_mutual_definitions
  :  info:Info.t
  -> cinfo: Constr.t CInfo.t list
  -> opaque:bool
  -> uctx:UState.t
  -> bodies:Constr.t list
  -> possible_guard:Pretyping.possible_guard * Sorts.relevance list
  -> ?using:Vernacexpr.section_subset_expr
  -> unit
  -> Names.GlobRef.t list

(** {2 Declaration of interactive constants }  *)

(** [save] / [save_admitted] can update obligations state, so we need
   to expose the state here *)
module OblState : sig

  type t
  val empty : t

  module View : sig
    module Obl : sig
      type t = private
        { name : Id.t
        ; loc : Loc.t option
        ; status : bool * Evar_kinds.obligation_definition_status
        ; solved : bool
        }
    end

    type t = private
      { opaque : bool
      ; remaining : int
      ; obligations : Obl.t array
      }
  end

  val view : t -> View.t Id.Map.t

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
    -> ?using:Id.Set.t
    -> Evd.evar_map
    -> t

  (** [start_{derive,equations}] are functions meant to handle
     interactive proofs with multiple goals, they should be considered
     experimental until we provide a more general API encompassing
     both of them. Please, get in touch with the developers if you
     would like to experiment with multi-goal dependent proofs so we
     can use your input on the design of the new API. *)
  val start_derive : name:Id.t -> info:Info.t -> cinfo:unit CInfo.t list -> Proofview.telescope -> t

  val start_equations :
       name:Id.t
    -> info:Info.t
    -> hook:(pm:OblState.t -> Constant.t list -> Evd.evar_map -> OblState.t)
    -> types:(Environ.env * Evar.t * Evd.undefined Evd.evar_info * EConstr.named_context * Evd.econstr) list
    -> Evd.evar_map
    -> Proofview.telescope
    -> t

  (** Pretty much internal, used by the Lemma vernaculars *)
  val start_definition
    :  info:Info.t
    -> cinfo:Constr.t CInfo.t
    -> ?using:Vernacexpr.section_subset_expr
    -> Evd.evar_map
    -> t

  (** Pretty much internal, used by mutual Lemma / Fixpoint vernaculars *)
  val start_mutual_definitions
    :  info:Info.t
    -> cinfo:Constr.t CInfo.t list
    -> bodies:Constr.t option list
    -> possible_guard:(Pretyping.possible_guard * Sorts.relevance list)
    -> ?using:Vernacexpr.section_subset_expr
    -> Evd.evar_map
    -> t

  (** Qed a proof  *)
  val save
    : pm:OblState.t
    -> proof:t
    -> opaque:Vernacexpr.opacity_flag
    -> idopt:Names.lident option
    -> OblState.t * GlobRef.t list

  (** For proofs known to have [Regular] ending, no need to touch program state. *)
  val save_regular
    : proof:t
    -> opaque:Vernacexpr.opacity_flag
    -> idopt:Names.lident option
    -> GlobRef.t list

  (** Admit a proof *)
  val save_admitted : pm:OblState.t -> proof:t -> OblState.t

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

  val definition_scope : t -> Locality.definition_scope

  (** Sets the section variables assumed by the proof, returns its closure
   * (w.r.t. type dependencies and let-ins covered by it) *)
  val set_proof_using : t -> Vernacexpr.section_subset_expr -> Constr.named_context * t

  (** Gets the set of variables declared to be used by the proof. None means
      no "Proof using" or #[using] was given *)
  val get_used_variables : t -> Id.Set.t option

  (** Compacts the representation of the proof by pruning all intermediate
      terms *)
  val compact : t -> t

  (** Update the proof's universe information typically after a
      side-effecting command (e.g. a sublemma definition) has been run
      inside it. *)
  val update_sigma_univs : UGraph.t -> t -> t

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

  (** {2 Proof delay API, warning, internal, not stable} *)

  (* Intermediate step necessary to delegate the future.
   * Both access the current proof state. The former is supposed to be
   * chained with a computation that completed the proof *)
  type closed_proof_output

  (** Requires a complete proof. *)
  val return_proof : t -> closed_proof_output

  (** XXX: This is an internal, low-level API and could become scheduled
      for removal from the public API, use higher-level declare APIs
      instead *)
  type proof_object

  val close_proof : ?warn_incomplete:bool -> opaque:Vernacexpr.opacity_flag -> keep_body_ucst_separate:bool -> t -> proof_object
  val close_future_proof : feedback_id:Stateid.t -> t -> closed_proof_output Future.computation -> proof_object

  (** Special cases for delayed proofs, in this case we must provide the
      proof information so the proof won't be forced. *)
  val save_lemma_admitted_delayed :
       pm:OblState.t
    -> proof:proof_object
    -> OblState.t

  val save_lemma_proved_delayed
    : pm:OblState.t
    -> proof:proof_object
    -> idopt:Names.lident option
    -> OblState.t

  exception NotGuarded of
      Environ.env * Evd.evar_map *
      (Environ.env * int * EConstr.t Type_errors.pcofix_guard_error) option *
      (Environ.env * int * int list * EConstr.t Type_errors.pfix_guard_error) list *
      EConstr.rec_declaration

  val control_only_guard : t -> unit

end

(** {2 low-level, internal API, avoid using unless you have special needs } *)

(** Proof entries represent a proof that has been finished, but still
   not registered with the kernel.

   XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
type proof_entry
type parameter_entry
type primitive_entry
type symbol_entry

val definition_entry
  :  ?opaque:bool
  -> ?using:Names.Id.Set.t
  -> ?inline:bool
  -> ?types:Constr.types
  -> ?univs:UState.named_universes_entry
  -> Constr.constr
  -> proof_entry

val parameter_entry
  :  ?inline:int
  -> ?univs:UState.named_universes_entry
  -> Constr.constr
  -> parameter_entry

val primitive_entry
  :  ?types:(Constr.types * UState.named_universes_entry)
  -> CPrimitives.op_or_type
  -> primitive_entry

val symbol_entry
  :  ?univs:UState.named_universes_entry
  -> unfold_fix:bool
  -> Constr.types
  -> symbol_entry

(** XXX: This is an internal, low-level API and could become scheduled
    for removal from the public API, use higher-level declare APIs
    instead *)
val declare_entry
  : ?loc:Loc.t
  -> name:Id.t
  -> ?scope:Locality.definition_scope
  -> kind:Decls.logical_kind
  -> ?user_warns:Globnames.extended_global_reference UserWarn.with_qf
  -> ?hook:Hook.t
  -> impargs:Impargs.manual_implicits
  -> uctx:UState.t
  -> proof_entry
  -> GlobRef.t

(** Declaration of section variables and local definitions *)
type variable_declaration =
  | SectionLocalDef of {
      clearbody : bool;
      entry : proof_entry;
    }
  | SectionLocalAssum of {
      typ : Constr.types;
      impl : Glob_term.binding_kind;
      univs : UState.named_universes_entry;
    }

(** Declaration of local constructions (Variable/Hypothesis/Local) *)
val declare_variable
  :  name:variable
  -> kind:Decls.logical_kind
  -> typing_flags:Declarations.typing_flags option
  -> variable_declaration
  -> unit

(** Declaration of global constructions
   i.e. Definition/Theorem/Axiom/Parameter/...

   XXX: This is an internal, low-level API and could become scheduled
   for removal from the public API, use higher-level declare APIs
   instead *)
type constant_entry =
  | DefinitionEntry of proof_entry
  | ParameterEntry of parameter_entry
  | PrimitiveEntry of primitive_entry
  | SymbolEntry of symbol_entry

val prepare_parameter
  : poly:bool
  -> udecl:UState.universe_decl
  -> types:EConstr.types
  -> Evd.evar_map
  -> Evd.evar_map * parameter_entry

(** [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration

  XXX: This is an internal, low-level API and could become scheduled
  for removal from the public API, use higher-level declare APIs
  instead *)
val declare_constant
  : ?loc:Loc.t
  -> ?local:Locality.import_status
  -> name:Id.t
  -> kind:Decls.logical_kind
  -> ?typing_flags:Declarations.typing_flags
  -> ?user_warns:Globnames.extended_global_reference UserWarn.with_qf
  -> constant_entry
  -> Constant.t

(** Like [declare_definition] but also returns the universes and universe constraints added to the
    global environment *)
val declare_definition_full
  :  info:Info.t
  -> cinfo:EConstr.t option CInfo.t
  -> opaque:bool
  -> body:EConstr.t
  -> ?using:Vernacexpr.section_subset_expr
  -> Evd.evar_map
  -> GlobRef.t * Univ.ContextSet.t

(** Declaration messages, for internal use *)

(** XXX: Scheduled for removal from public API, do not use *)
val definition_message : Id.t -> unit
val assumption_message : Id.t -> unit
val fixpoint_message : int array option -> Id.t list -> unit

val check_exists : Id.t -> unit

(** Semantics of this function is a bit dubious, use with care *)
val build_by_tactic
  :  Environ.env
  -> uctx:UState.t
  -> poly:bool
  -> typ:EConstr.types
  -> unit Proofview.tactic
  -> Constr.constr * Constr.types option * UState.named_universes_entry * bool * UState.t

(** {2 Program mode API} *)

(** Rocq's Program mode support. This mode extends declarations of
   constants and fixpoints with [Program Definition] and [Program
   Fixpoint] to support incremental construction of terms using
   delayed proofs, called "obligations"

    The mode also provides facilities for managing and auto-solving
   sets of obligations.

    The basic code flow of programs/obligations is as follows:

    - [add_definition] / [add_mutual_definitions] are called from the
   respective [Program] vernacular command interpretation; at this
   point the only extra work we do is to prepare the new definition
   [d] using [RetrieveObl], which consists in turning unsolved evars
   into obligations. [d] is not sent to the kernel yet, as it is not
   complete and cannot be typchecked, but saved in a special
   data-structure. Auto-solving of obligations is tried at this stage
   (see below)

   - [next_obligation] will retrieve the next obligation
   ([RetrieveObl] sorts them by topological order) and will try to
   solve it. When all obligations are solved, the original constant
   [d] is grounded and sent to the kernel for addition to the global
   environment. Auto-solving of obligations is also triggered on
   obligation completion.

{2} Solving of obligations: Solved obligations are stored as regular
   global declarations in the global environment, usually with name
   [constant_obligation_number] where [constant] is the original
   [constant] and [number] is the corresponding (internal) number.

   Solving an obligation can trigger a bit of a complex cascaded
   callback path; closing an obligation can indeed allow all other
   obligations to be closed, which in turn may trigged the declaration
   of the original constant. Care must be taken, as this can modify
   [Global.env] in arbitrarily ways. Current code takes some care to
   refresh the [env] in the proper boundaries, but the invariants
   remain delicate.

{2} Saving of obligations: as open obligations use the regular proof
   mode, a `Qed` will call `Lemmas.save_lemma` first. For this reason
   obligations code is split in two: this file, [Obligations], taking
   care of the top-level vernac commands, and [Declare], which is
   called by `Lemmas` to close an obligation proof and eventually to
   declare the top-level [Program]ed constant.

 *)

module Obls : sig

type fixpoint_kind = IsFixpoint of lident option list | IsCoFixpoint

(** Check obligations are properly solved before closing the
   [what_for] section / module *)
val check_solved_obligations : pm:OblState.t -> what_for:Pp.t -> unit
val default_tactic : unit Proofview.tactic ref

(** Resolution status of a program *)
type progress =
  | Remain of int  (** n obligations remaining *)
  | Dependent  (** Dependent on other definitions *)
  | Defined of GlobRef.t  (** Defined as id *)

(** Prepare API, to be removed once we provide the corresponding 1-step API *)
val prepare_obligations
  :  name:Id.t
  -> ?types:EConstr.t
  -> body:EConstr.t
  -> Environ.env
  -> Evd.evar_map
  -> Constr.constr * Constr.types * UState.t * RetrieveObl.obligation_name_lifter * RetrieveObl.obligation_info

(** Start a [Program Definition c] proof. [uctx] [udecl] [impargs]
   [kind] [scope] [poly] etc... come from the interpretation of the
   vernacular; `obligation_info` was generated by [RetrieveObl] It
   will return whether all the obligations were solved; if so, it will
   also register [c] with the kernel. *)
val add_definition :
     pm:OblState.t
  -> info:Info.t
  -> cinfo:Constr.types CInfo.t
  -> opaque:bool
  -> uctx:UState.t
  -> ?body:Constr.t
  -> ?tactic:unit Proofview.tactic
  -> ?reduce:(Constr.t -> Constr.t)
  -> ?using:Vernacexpr.section_subset_expr
  -> ?obl_hook: OblState.t Hook.g
  -> RetrieveObl.obligation_info
  -> OblState.t * progress

(* XXX: unify with MutualEntry *)

(** Start a [Program Fixpoint] declaration, similar to the above,
   except it takes a list now. *)
val add_mutual_definitions :
     pm:OblState.t
  -> info:Info.t
  -> cinfo:Constr.types CInfo.t list
  -> opaque:bool
  -> uctx:UState.t
  -> bodies:Constr.t list
  -> possible_guard:(Pretyping.possible_guard * Sorts.relevance list)
  -> ?tactic:unit Proofview.tactic
  -> ?reduce:(Constr.t -> Constr.t)
  -> ?using:Vernacexpr.section_subset_expr
  -> ?obl_hook: OblState.t Hook.g
  -> RetrieveObl.obligation_info list
  -> OblState.t

(** Implementation of the [Obligation n of id with tac] command *)
val obligation :
     int * Names.Id.t option
  -> pm:OblState.t
  -> Genarg.glob_generic_argument option
  -> Proof.t

(** Implementation of the [Next Obligation of id with tac] and [Final Obligation of id with tac] commands *)
val next_obligation :
  pm:OblState.t -> ?final:bool -> Names.Id.t option -> Genarg.glob_generic_argument option -> Proof.t

(** Implementation of the [Solve Obligations of id with tac] command *)
val solve_obligations :
  pm:OblState.t -> Names.Id.t option -> unit Proofview.tactic option -> OblState.t * progress
val try_solve_obligations :
  pm:OblState.t -> Names.Id.t option -> unit Proofview.tactic option -> OblState.t

(** Implementation of the [Solve All Obligations with tac] command *)
val solve_all_obligations : pm:OblState.t -> unit Proofview.tactic option -> OblState.t

(** Implementation of the [Obligations of id] command *)
val show_obligations : pm:OblState.t -> ?msg:bool -> Names.Id.t option -> unit

(** Implementation of the [Preterm of id] command *)
val show_term : pm:OblState.t -> Names.Id.t option -> Pp.t

(** Implementation of the [Admit Obligations of id] command *)
val admit_obligations : pm:OblState.t -> Names.Id.t option -> OblState.t

val check_program_libraries : unit -> unit

val program_inference_hook : Environ.env -> Evd.evar_map -> Evar.t -> (Evd.evar_map * EConstr.t) option

end

val is_local_constant : Constant.t -> bool

(** {6 For internal support, do not use}  *)

module Internal : sig

  (* Libobject exports *)
  module Constant : sig
    type t
    val tag : (Id.t * t) Libobject.Dyn.tag
    val kind : t -> Decls.logical_kind
  end

  val objVariable : Id.t Libobject.Dyn.tag

  (** [export_side_effects eff] makes the side effects [eff] global. This
    usually happens at the end of a proof (during Qed or Defined), but
    one may need to declare them by hand, for example because the
    tactic was run as part of a command *)
  val export_side_effects : Evd.side_effects -> unit

end
