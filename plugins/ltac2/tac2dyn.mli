(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Dynamic arguments for Ltac2. *)

module Arg :
sig
  type ('a, 'b) tag
  val create : string -> ('a, 'b) tag
  val eq : ('a1, 'b1) tag -> ('a2, 'b2) tag -> ('a1 * 'b1, 'a2 * 'b2) CSig.eq option
  val repr : ('a, 'b) tag -> string
  type glb = Glb : (_,'a) tag * 'a  -> glb
end
(** Arguments that are part of an AST. *)

module type Param = sig type ('raw, 'glb) t end

module ArgMap (M : Param) :
sig
  type _ pack = Pack : ('raw, 'glb) M.t -> ('raw * 'glb) pack
  type t
  val empty : t
  val add : ('a, 'b) Arg.tag -> ('a * 'b) pack -> t -> t
  val remove : ('a, 'b) Arg.tag -> t -> t
  val find : ('a, 'b) Arg.tag -> t -> ('a * 'b) pack
  val mem : ('a, 'b) Arg.tag -> t -> bool
end

module Val : Dyn.S
(** Toplevel values *)
