(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t
(** Type of canaries. Canaries are used to ensure that an object does not use
    generic operations. *)

val obj : t
(** Canary. In the current implementation, this object is marshallable,
    forbids generic comparison but still allows generic hashes. *)

module type Obj = sig type t end

module Make(M : Obj) :
sig
  type t
  val prj : t -> M.t
  val inj : M.t -> t
end
(** Adds a canary to any type. *)
