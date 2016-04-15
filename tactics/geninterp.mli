(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Interpretation functions for generic arguments. *)

open Names
open Genarg

module TacStore : Store.S

type interp_sign = {
  lfun : Val.t Id.Map.t;
  extra : TacStore.t }

type ('glb, 'top) interp_fun = interp_sign -> 'glb -> 'top Ftactic.t

val interp : ('raw, 'glb, 'top) genarg_type -> ('glb, 'top) interp_fun

val generic_interp : (glob_generic_argument, Val.t) interp_fun

val register_interp0 :
  ('raw, 'glb, 'top) genarg_type -> ('glb, 'top) interp_fun -> unit
