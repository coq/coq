(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val apply_tooltip_tag :
  GText.buffer ->
  start:GText.iter -> stop:GText.iter ->
  markup:string lazy_t -> unit

val set_tooltip_callback : GText.view -> unit
