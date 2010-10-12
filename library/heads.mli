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

(** This module is about the computation of an approximation of the
    head symbol of defined constants and local definitions; it
    provides the function to compute the head symbols and a table to
    store the heads *)

(** [declared_head] computes and registers the head symbol of a
   possibly evaluable constant or variable *)

val declare_head : evaluable_global_reference -> unit

(** [is_rigid] tells if some term is known to ultimately reduce to a term
    with a rigid head symbol *)

val is_rigid : env -> constr -> bool
