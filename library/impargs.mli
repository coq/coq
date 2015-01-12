(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Globnames
open Term
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

type implicits_flags
val with_implicits : implicits_flags -> ('a -> 'b) -> 'a -> 'b

(** {6 ... } *)
(** An [implicits_list] is a list of positions telling which arguments
    of a reference can be automatically infered *)


type argument_position =
  | Conclusion
  | Hyp of int

(** We remember various information about why an argument is
   inferable as implicit *)
type implicit_explanation =
  | DepRigid of argument_position
      (** means that the implicit argument can be found by
	  unification along a rigid path (we do not print the arguments of
	  this kind if there is enough arguments to infer them) *)
  | DepFlex of argument_position
      (** means that the implicit argument can be found by unification
	  along a collapsable path only (e.g. as x in (P x) where P is another
	  argument) (we do (defensively) print the arguments of this kind) *)
  | DepFlexAndRigid of (*flex*) argument_position * (*rig*) argument_position
      (** means that the least argument from which the
	  implicit argument can be inferred is following a collapsable path
	  but there is a greater argument from where the implicit argument is
	  inferable following a rigid path (useful to know how to print a
	  partial application) *)
  | Manual
      (** means the argument has been explicitely set as implicit. *)
      
(**  We also consider arguments inferable from the conclusion but it is
     operational only if [conclusion_matters] is true. *)

type maximal_insertion = bool (** true = maximal contextual insertion *)
type force_inference = bool (** true = always infer, never turn into evar/subgoal *)

type implicit_status = (Id.t * implicit_explanation * 
			  (maximal_insertion * force_inference)) option
    (** [None] = Not implicit *)

type implicit_side_condition

type implicits_list = implicit_side_condition * implicit_status list

val is_status_implicit : implicit_status -> bool
val is_inferable_implicit : bool -> int -> implicit_status -> bool
val name_of_implicit : implicit_status -> Id.t
val maximal_insertion_of : implicit_status -> bool
val force_inference_of : implicit_status -> bool

val positions_of_implicits : implicits_list -> int list

(** A [manual_explicitation] is a tuple of a positional or named explicitation with
   maximal insertion, force inference and force usage flags. Forcing usage makes
   the argument implicit even if the automatic inference considers it not inferable. *)
type manual_explicitation = Constrexpr.explicitation *
    (maximal_insertion * force_inference * bool)

type manual_implicits = manual_explicitation list

val compute_implicits_with_manual : env -> types -> bool ->
  manual_implicits -> implicit_status list

val compute_implicits_names : env -> types -> Name.t list

(** {6 Computation of implicits (done using the global environment). } *)

val declare_var_implicits : variable -> unit
val declare_constant_implicits : constant -> unit
val declare_mib_implicits : mutual_inductive -> unit

val declare_implicits : bool -> global_reference -> unit

(** [declare_manual_implicits local ref enriching l]
   Manual declaration of which arguments are expected implicit.
   If not set, we decide if it should enrich by automatically inferd
   implicits depending on the current state.
   Unsets implicits if [l] is empty. *)

val declare_manual_implicits : bool -> global_reference -> ?enriching:bool ->
  manual_implicits list -> unit

(** If the list is empty, do nothing, otherwise declare the implicits. *)

val maybe_declare_manual_implicits : bool -> global_reference -> ?enriching:bool ->
  manual_implicits -> unit

val implicits_of_global : global_reference -> implicits_list list

val extract_impargs_data :
  implicits_list list -> ((int * int) option * implicit_status list) list

val lift_implicits : int -> manual_implicits -> manual_implicits

val make_implicits_list : implicit_status list -> implicits_list list

val drop_first_implicits : int -> implicits_list -> implicits_list

val projection_implicits : env -> projection -> implicit_status list -> 
  implicit_status list

val select_impargs_size : int -> implicits_list list -> implicit_status list

val select_stronger_impargs : implicits_list list -> implicit_status list

type implicit_interactive_request

type implicit_discharge_request =
  | ImplLocal
  | ImplConstant of constant * implicits_flags
  | ImplMutualInductive of mutual_inductive * implicits_flags
  | ImplInteractive of global_reference * implicits_flags *
      implicit_interactive_request

val explicitation_eq : Constrexpr.explicitation -> Constrexpr.explicitation -> bool
(** Equality on [explicitation]. *)
