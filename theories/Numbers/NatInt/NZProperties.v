(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export NZAxioms NZMulOrder.

(** This functor summarizes all known facts about NZ.
    For the moment it is only an alias to [NZMulOrderPropFunct], which
    subsumes all others.
*)

Module Type NZPropFunct := NZMulOrderPropSig.
