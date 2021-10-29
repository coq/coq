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
open EConstr
open Environ

(** {6 Implicit Arguments } *)
(** Here we store the implicit arguments. Notice that we
    are outside the kernel, which knows nothing about implicit arguments. *)

val make_implicit_args : bool -> unit
val make_strict_implicit_args : bool -> unit
val make_strongly_strict_implicit_args : bool -> unit
val make_reversible_pattern_implicit_args : bool -> unit
val make_contextual_implicit_args : bool -> unit
val make_maximal_implicit_args : bool -> unit

val is_implicit_args : unit -> bool
val is_strict_implicit_args : unit -> bool
val is_strongly_strict_implicit_args : unit -> bool
val is_reversible_pattern_implicit_args : unit -> bool
val is_contextual_implicit_args : unit -> bool
val is_maximal_implicit_args : unit -> bool

val with_implicit_protection : ('a -> 'b) -> 'a -> 'b

(** {6 ... } *)
(** An [implicits_list] is a list of positions telling which arguments
    of a reference can be automatically inferred *)


type argument_position =
  | Conclusion
  | Hyp of int

type dependency_explanation

(**  We also consider arguments inferable from the conclusion but it is
     operational only if [conclusion_matters] is true. *)

type maximal_insertion = bool (** true = maximal contextual insertion *)

type force_inference = bool (** true = always infer, never turn into evar/subgoal *)

type argument_status = Name.t * int option * dependency_explanation

type implicit_proper_status

type implicit_status = argument_status * implicit_proper_status option

    (** [None] = Not implicit *)
val default_implicit : maximal:bool -> force:bool -> implicit_proper_status
  (** maximal:true = maximal contextual insertion
      force:true = always infer, never turn into evar/subgoal *)

type implicit_side_condition

type implicits_list = implicit_side_condition * implicit_status list

val default_dependency_explanation : dependency_explanation
val is_status_implicit : implicit_status -> bool
val binding_kind_of_status : implicit_status -> Glob_term.binding_kind
val is_inferable_implicit : bool -> int -> implicit_status -> bool
val name_of_argument : int -> implicit_status -> Id.t
val match_argument : int -> implicit_status -> Constrexpr.explicitation -> bool
val maximal_insertion_of : implicit_status -> bool
val force_inference_of : implicit_status -> bool
val is_named_argument : Id.t -> implicit_status list -> bool
val is_nondep_argument : int -> implicit_status list -> bool
val explicitation : implicit_status -> Constrexpr.explicitation

val print_allowed_named_implicit : implicit_status list -> Pp.t
val print_allowed_nondep_implicit : implicit_status list -> Pp.t


type manual_implicits = (Name.t * bool) option CAst.t list

val compute_implicits_with_manual : env -> Evd.evar_map -> types ->
  manual_implicits -> implicit_status list

val compute_argument_names : env -> Evd.evar_map -> types -> Name.t list

(** {6 Computation of implicits (done using the global environment). } *)

val declare_var_implicits : variable -> impl:Glob_term.binding_kind -> unit
val declare_constant_implicits : Constant.t -> unit
val declare_mib_implicits : MutInd.t -> unit

val declare_implicits : bool -> GlobRef.t -> unit

(** [declare_manual_implicits local ref enriching l]
   Manual declaration of which arguments are expected implicit.
   If not set, we decide if it should enrich by automatically inferd
   implicits depending on the current state.
   Unsets implicits if [l] is empty. *)

val declare_manual_implicits : bool -> GlobRef.t ->
  manual_implicits -> unit

(** If the list is empty, do nothing, otherwise declare the implicits. *)

val maybe_declare_manual_implicits : bool -> GlobRef.t ->
  manual_implicits -> unit

(** [set_implicits local ref l]
   Manual declaration of implicit arguments.
  [l] is a list of possible sequences of implicit statuses. *)
val set_implicits : bool -> GlobRef.t -> (Name.t * Glob_term.binding_kind) list list -> unit

val implicits_of_global : GlobRef.t -> implicits_list list

val extract_impargs_data :
  implicits_list list -> ((int * int) option * implicit_status list) list

val make_implicits_list : implicit_status list -> implicits_list list

val drop_first_implicits : int -> implicits_list -> implicits_list

val projection_implicits : env -> Projection.t -> implicit_status list ->
  implicit_status list

val select_impargs_size : int -> implicits_list list -> implicit_status list

val select_stronger_impargs : implicits_list list -> implicit_status list

val select_impargs_size_for_proj :
  nexpectedparams:int -> ngivenparams:int -> nextraargs:int ->
  implicits_list list -> (implicit_status list * implicit_status list, int list Lazy.t) Util.union

val impargs_for_proj :
  nexpectedparams:int -> nextraargs:int ->
  implicit_status list -> implicit_status list * implicit_status list
