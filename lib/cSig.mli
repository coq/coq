(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Missing pervasive types from OCaml stdlib *)

type ('a, 'b) union = Inl of 'a | Inr of 'b
(** Union type *)

type ('a, 'b) seek = Stop of 'a | Next of 'b
(** Type isomorphic to union used for browsable structures. *)
