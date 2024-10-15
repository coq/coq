(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Legacy proof engine. Do not use in newly written code. *)

open Names
open Evd

(** [check] respectively means:\\
  [Intro]: check that the name does not exist\\
  [Intro_after]: check that the name does not exist and that variables in
     its type does not escape their scope\\
  [Intro_replacing]: check that the name does not exist and that
     variables in its type does not escape their scope\\
  [Convert_hyp]:
  check that the name exist and that its type is convertible\\
*)

(** {6 Refiner errors. } *)

type refiner_error =

  (*i Errors raised by the refiner i*)
  | UnresolvedBindings of Name.t list
  | CannotApply of EConstr.t * EConstr.t
  | NonLinearProof of EConstr.t

  (*i Errors raised by the tactics i*)
  | IntroNeedsProduct
  | NoSuchHyp of Id.t

exception RefinerError of Environ.env * evar_map * refiner_error

val error_no_such_hypothesis : Environ.env -> evar_map -> Id.t -> 'a

(** Move destination for hypothesis *)

type 'id move_location =
  | MoveAfter of 'id
  | MoveBefore of 'id
  | MoveFirst
  | MoveLast (** can be seen as "no move" when doing intro *)

val pr_move_location :
  ('a -> Pp.t) -> 'a move_location -> Pp.t

val convert_hyp : check:bool -> reorder:bool -> Environ.env -> evar_map ->
  EConstr.named_declaration -> Environ.named_context_val

type cannot_move_hyp
exception CannotMoveHyp of cannot_move_hyp

val move_hyp_in_named_context : Environ.env -> Evd.evar_map -> Id.t -> Id.t move_location ->
  Environ.named_context_val -> Environ.named_context_val

val insert_decl_in_named_context : Environ.env -> Evd.evar_map ->
  EConstr.named_declaration -> Id.t move_location ->
  Environ.named_context_val -> Environ.named_context_val
