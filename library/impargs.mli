(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Libnames
open Term
open Environ
open Nametab
(*i*)

(*s Implicit arguments. Here we store the implicit arguments. Notice that we 
    are outside the kernel, which knows nothing about implicit arguments. *)

val make_implicit_args : bool -> unit
val is_implicit_args : unit -> bool
val implicitly : ('a -> 'b) -> 'a -> 'b
val with_implicits : bool -> ('a -> 'b) -> 'a -> 'b

val strict_implicit_args : bool ref
val contextual_implicit_args : bool ref

(*s An [implicits_list] is a list of positions telling which arguments
    of a reference can be automatically infered *)
type implicit_status
type implicits_list = implicit_status list

val is_status_implicit : implicit_status -> bool
val is_inferable_implicit : int -> implicit_status -> bool
val positions_of_implicits : implicits_list -> int list

(* Computation of the positions of arguments automatically inferable
   for an object of the given type in the given env *)
val compute_implicits : env -> types -> implicits_list

(*s Computation of implicits (done using the global environment). *)

val declare_var_implicits : variable -> unit
val declare_constant_implicits : constant -> unit
val declare_mib_implicits : mutual_inductive -> unit
val declare_implicits : global_reference -> unit

(* Manual declaration of which arguments are expected implicit *)
val declare_manual_implicits : global_reference -> int list -> unit

(*s Access to already computed implicits. *)

val constructor_implicits_list : constructor -> implicits_list
val inductive_implicits_list : inductive -> implicits_list
val constant_implicits_list : constant -> implicits_list

val implicits_of_var : variable -> implicits_list

val is_implicit_constant : constant -> bool
val is_implicit_inductive_definition : inductive -> bool
val is_implicit_var : variable -> bool

val implicits_of_global : global_reference -> implicits_list

(*s Rollback. *)

type frozen_t
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit
