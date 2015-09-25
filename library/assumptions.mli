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
open Globnames

(** A few declarations for the "Print Assumption" command
    @author spiwack *)
type axiom =
  | Constant of constant (** An axiom or a constant. *)
  | Positive of MutInd.t (** A mutually inductive definition which has been assumed positive. *)
  | Guarded of constant (** A constant whose (co)fixpoints have been assumed to be guarded *)
type context_object =
  | Variable of Id.t  (** A section variable or a Let definition. *)
  | Axiom of axiom       (** An assumed fact. *)
  | Opaque of constant      (** An opaque constant. *)
  | Transparent of constant (** A transparent constant *)

(** AssumptionSet.t is a set of [assumption] *)
module ContextObjectSet : Set.S with type elt = context_object
module ContextObjectMap : Map.ExtS
  with type key = context_object and module Set := ContextObjectSet

(** Collects all the objects on which a term directly relies, bypassing kernel
    opacity, together with the recursive dependence DAG of objects.

    WARNING: some terms may not make sense in the environment, because they are
    sealed inside opaque modules. Do not try to do anything fancy with those
    terms apart from printing them, otherwise demons may fly out of your nose.
*)
val traverse : constr -> (Refset.t * Refset.t Refmap.t)

(** Collects all the assumptions (optionally including opaque definitions)
   on which a term relies (together with their type). The above warning of
   {!traverse} also applies. *)
val assumptions :
  ?add_opaque:bool -> ?add_transparent:bool -> transparent_state -> constr ->
    Term.types ContextObjectMap.t
