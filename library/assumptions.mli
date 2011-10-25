(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ

(** A few declarations for the "Print Assumption" command
    @author spiwack *)
type context_object =
  | Variable of identifier (** A section variable or a Let definition *)
  | Axiom of constant      (** An axiom or a constant. *)
  | Opaque of constant     (** An opaque constant. *)

(** AssumptionSet.t is a set of [assumption] *)
module OrderedContextObject :  Set.OrderedType with type t = context_object
module ContextObjectMap : Map.S with type key = context_object

(** collects all the assumptions (optionally including opaque definitions)
   on which a term relies (together with their type) *)
val assumptions :
  ?add_opaque:bool -> transparent_state -> constr ->
    Term.types ContextObjectMap.t
