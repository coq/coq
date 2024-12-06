(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Attributes deprecated(since="8.20", note="use Stdlib.Numbers.NatInt.NZMulOrder instead").
Require Export NZAxioms NZMulOrder.

(** This functor summarizes all known facts about NZ.
    For the moment it is only an alias to [NZMulOrderProp], which
    subsumes all others.
*)

Module Type NZProp := NZMulOrderProp.
