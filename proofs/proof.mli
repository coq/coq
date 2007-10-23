(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: proof.mli aspiwack $ *)

(* This module implements the actual proof datatype. It enforces strong
   invariants, and it is the only module that should access the module
   Subproof.
   Actually from outside the proofs/ subdirectory, this is the only module
   that should be used directly. *)

open Term

(* Type of a proof *)
type 'a proof

(* Type of the proof transformations *)
type 'a transformation

(* exception which represent a failure in a command.
   Opposed to anomalies and uncaught exceptions. *)
exception Failure of Pp.std_ppcmds

(* function to raise a failure less verbosely *)
val fail : Pp.std_ppcmds -> 'a

val do_command : 'a transformation -> 'a proof -> unit


