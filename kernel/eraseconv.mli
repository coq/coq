(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Conversion

val erase_eval : Environ.env -> Constr.t -> (Constr.t, unit) result

val erase_conv : conv_pb -> types kernel_conversion_function

(** The erase evaluation function can either return an evaluated term or an error if the
    evaluated term cannot be read back *)
type erase_evaluation_function =
  Environ.env -> Constr.t -> types -> (Constr.t, unit) result

(** Link a specific evaluation function. By default it is the function always returning an error. *)
val install_erase_conv : erase_evaluation_function -> unit
