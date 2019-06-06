(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Environ

(** This module is about the computation of an approximation of the
    head symbol of defined constants and local definitions; it
    provides the function to compute the head symbols and a table to
    store the heads *)

(** [is_rigid] tells if some term is known to ultimately reduce to a term
    with a rigid head symbol *)

val is_rigid : env -> constr -> bool
