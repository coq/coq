(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Regular intern using the filesystem  *)
val fs_intern : Library.Intern.t

(** The main interpretation function of vernacular expressions *)
val interp
  : intern:Library.Intern.t
  -> ?verbosely:bool
  -> st:Vernacstate.t
  -> Vernacexpr.vernac_control
  -> Vernacstate.t

val interp_entry
  : ?verbosely:bool
  -> st:Vernacstate.t
  -> Synterp.vernac_control_entry
  -> Vernacstate.Interp.t

(** Execute a Qed but with a proof_object which may contain a delayed
   proof and won't be forced *)
val interp_qed_delayed_proof
  :  proof:Declare.Proof.proof_object
  -> st:Vernacstate.t
  -> control:unit VernacControl.control_entries
  -> Vernacexpr.proof_end CAst.t
  -> Vernacstate.Interp.t
