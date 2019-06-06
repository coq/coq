(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ

exception InductiveMismatch of MutInd.t * string
(** Some field of the inductive is different from what the kernel infers. *)

(*s The following function does checks on inductive declarations. *)

val check_inductive : env -> MutInd.t -> Declarations.mutual_inductive_body -> env
