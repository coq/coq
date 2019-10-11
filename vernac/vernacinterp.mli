(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The main interpretation function of vernacular expressions *)
val interp : ?verbosely:bool -> st:Vernacstate.t -> Vernacexpr.vernac_control -> Vernacstate.t

(** Execute a Qed but with a proof_object which may contain a delayed
   proof and won't be forced *)
val interp_qed_delayed_proof
  :  proof:Proof_global.proof_object
  -> info:Lemmas.Info.t
  -> st:Vernacstate.t
  -> control:Vernacexpr.control_flag list
  -> Vernacexpr.proof_end CAst.t
  -> Vernacstate.t

(** [with_fail ~st f] runs [f ()] and expects it to fail, otherwise it fails. *)
val with_fail : st:Vernacstate.t -> (unit -> 'a) -> unit

(** Flag set when the test-suite is called. Its only effect to display
    verbose information for [Fail] *)
val test_mode : bool ref

(** Default proof mode set by `start_proof` *)
val get_default_proof_mode : unit -> Pvernac.proof_mode
val proof_mode_opt_name : string list
