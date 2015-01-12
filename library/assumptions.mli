(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term

(** A few declarations for the "Print Assumption" command
    @author spiwack *)
type context_object =
  | Variable of Id.t  (** A section variable or a Let definition *)
  | Axiom of constant       (** An axiom or a constant. *)
  | Opaque of constant      (** An opaque constant. *)
  | Transparent of constant (** A transparent constant *)

(** AssumptionSet.t is a set of [assumption] *)
module ContextObjectSet : Set.S with type elt = context_object
module ContextObjectMap : Map.ExtS
  with type key = context_object and module Set := ContextObjectSet

(** collects all the assumptions (optionally including opaque definitions)
   on which a term relies (together with their type) *)
val assumptions :
  ?add_opaque:bool -> ?add_transparent:bool -> transparent_state -> constr ->
    Term.types ContextObjectMap.t
