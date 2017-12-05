(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Constr
open Univ

(** The universes of monomorphic constants appear. *)
val universes_of_constr : Environ.env -> constr -> LSet.t

(** Shrink a universe context to a restricted set of variables *)
val restrict_universe_context : ContextSet.t -> LSet.t -> ContextSet.t
