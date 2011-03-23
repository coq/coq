(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Specialize loop of Coqtop for interaction with CoqIde *)

val reinit : unit -> unit

val init_stdout : unit -> unit

val eval_call : 'a Ide_intf.call -> 'a Ide_intf.value

val loop : unit -> unit
