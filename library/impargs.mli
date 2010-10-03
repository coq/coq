(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames
open Term
open Environ
open Nametab

(** Implicit Arguments *)

(** {6 ... } *)
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

type implicit_explanation =
  | DepRigid of argument_position
  | DepFlex of argument_position
  | DepFlexAndRigid of (*flex*) argument_position * (*rig*) argument_position
  | Manual

type implicit_status = (identifier * implicit_explanation * (bool * bool)) option
type implicits_list = implicit_status list

val is_status_implicit : implicit_status -> bool
val is_inferable_implicit : bool -> int -> implicit_status -> bool
val name_of_implicit : implicit_status -> identifier
val maximal_insertion_of : implicit_status -> bool
val force_inference_of : implicit_status -> bool

val positions_of_implicits : implicits_list -> int list

(** Computation of the positions of arguments automatically inferable
   for an object of the given type in the given env *)
val compute_implicits : env -> types -> implicits_list

(** A [manual_explicitation] is a tuple of a positional or named explicitation with
   maximal insertion, force inference and force usage flags. Forcing usage makes
   the argument implicit even if the automatic inference considers it not inferable. *)
type manual_explicitation = Topconstr.explicitation * (bool * bool * bool)

val compute_implicits_with_manual : env -> types -> bool ->
  manual_explicitation list -> implicits_list

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
  manual_explicitation list -> unit

(** If the list is empty, do nothing, otherwise declare the implicits. *)

val maybe_declare_manual_implicits : bool -> global_reference -> ?enriching:bool ->
  manual_explicitation list -> unit

val implicits_of_global : global_reference -> implicits_list

val lift_implicits : int -> manual_explicitation list -> manual_explicitation list

val merge_impls : implicits_list -> implicits_list -> implicits_list

type implicit_interactive_request =
  | ImplAuto
  | ImplManual

type implicit_discharge_request =
  | ImplLocal
  | ImplConstant of constant * implicits_flags
  | ImplMutualInductive of mutual_inductive * implicits_flags
  | ImplInteractive of global_reference * implicits_flags *
      implicit_interactive_request

