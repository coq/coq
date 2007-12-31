(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

(*s An [implicits_list] is a list of positions telling which arguments
    of a reference can be automatically infered *)
type implicit_status
type implicits_list = implicit_status list

type implicit_explanation

val is_status_implicit : implicit_status -> bool
val is_inferable_implicit : bool -> int -> implicit_status -> bool
val name_of_implicit : implicit_status -> identifier
val maximal_insertion_of : implicit_status -> bool
val forced_implicit : implicit_status -> bool

val positions_of_implicits : implicits_list -> int list

(* Computation of the positions of arguments automatically inferable
   for an object of the given type in the given env *)
val compute_implicits : env -> types -> implicits_list

(*s Computation of implicits (done using the global environment). *)

val declare_var_implicits : variable -> unit
val declare_constant_implicits : constant -> unit
val declare_mib_implicits : mutual_inductive -> unit

val declare_implicits : bool -> global_reference -> unit

(* A [manual_explicitation] is a tuple of a positional or named explicitation with
   maximal insertion and forcing flags. *)
type manual_explicitation = Topconstr.explicitation * (bool * bool) 

(* Manual declaration of which arguments are expected implicit *)
val declare_manual_implicits : bool -> global_reference -> bool ->
  manual_explicitation list -> unit

val implicits_of_global : global_reference -> implicits_list

