(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Legacy proof engine. Do not use in newly written code. *)

open Names
open Constr
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

(** The primitive refiner. *)

val prim_refiner : check:bool -> constr -> evar_map -> Goal.goal -> Goal.goal list * evar_map

(** {6 Refiner errors. } *)

type refiner_error =

  (*i Errors raised by the refiner i*)
  | BadType of constr * constr * constr
  | UnresolvedBindings of Name.t list
  | CannotApply of constr * constr
  | NotWellTyped of constr
  | NonLinearProof of constr
  | MetaInType of EConstr.constr

  (*i Errors raised by the tactics i*)
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * Id.t
  | NoSuchHyp of Id.t

exception RefinerError of Environ.env * evar_map * refiner_error

val error_no_such_hypothesis : Environ.env -> evar_map -> Id.t -> 'a

val catchable_exception : exn -> bool

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

val move_hyp_in_named_context : Environ.env -> Evd.evar_map -> Id.t -> Id.t move_location ->
  Environ.named_context_val -> Environ.named_context_val

val insert_decl_in_named_context : Environ.env -> Evd.evar_map ->
  EConstr.named_declaration -> Id.t move_location ->
  Environ.named_context_val -> Environ.named_context_val
