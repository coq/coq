(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Declarations
open Environ
open Entries

(** Check an inductive. *)
val check_inductive : env -> sec_univs:UVars.Instance.t option
  -> MutInd.t -> mutual_inductive_entry
  -> mutual_inductive_body * IndTyping.NotPrimRecordReason.t option
