(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.4 *)

(** Sometimes, we need to use [shelve] or [shelve_unifiable] in Coq
    v8.5 to pretend that we're Coq v8.4.  So we define them to be
    [idtac] here, so that they don't throw up errors about being
    undefined. *)
Ltac shelve_unifiable := idtac.
Ltac shelve := idtac.
