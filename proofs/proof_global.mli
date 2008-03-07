(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(***********************************************************************)
(*                                                                     *)
(*      This module defines the global proof environment               *)
(*      Especially it keeps tracks of whether or not there is          *)
(*      a proof which is currently being edited.                       *)
(*                                                                     *)
(***********************************************************************)


val is_there_a_proof : unit -> bool
