(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val xlra_Q : unit Proofview.tactic -> unit Proofview.tactic
val xlra_R : unit Proofview.tactic -> unit Proofview.tactic
val xlia : unit Proofview.tactic -> unit Proofview.tactic
val xnra_Q : unit Proofview.tactic -> unit Proofview.tactic
val xnra_R : unit Proofview.tactic -> unit Proofview.tactic
val xnia : unit Proofview.tactic -> unit Proofview.tactic
val xsos_Q : unit Proofview.tactic -> unit Proofview.tactic
val xsos_R : unit Proofview.tactic -> unit Proofview.tactic
val xsos_Z : unit Proofview.tactic -> unit Proofview.tactic
val xpsatz_Q : int -> unit Proofview.tactic -> unit Proofview.tactic
val xpsatz_R : int -> unit Proofview.tactic -> unit Proofview.tactic
val xpsatz_Z : int -> unit Proofview.tactic -> unit Proofview.tactic
val print_lia_profile : unit -> unit

(** {5 Use Micromega independently from micromega parser. } *)

(** [wlra_Q id ff] takes a formula [ff : BFormula (Formula Q) isProp]
    generates a witness and poses it as [id : seq (Psatz Q)] *)
val wlra_Q : Names.Id.t -> EConstr.t -> unit Proofview.tactic

(** [wlia id ff] takes a formula [ff : BFormula (Formula Z) isProp]
    generates a witness and poses it as [id : seq ZMicromega.ZArithProof] *)
val wlia : Names.Id.t -> EConstr.t -> unit Proofview.tactic

(** [wnra_Q id ff] takes a formula [ff : BFormula (Formula Q) isProp]
    generates a witness and poses it as [id : seq (Psatz Q)] *)
val wnra_Q : Names.Id.t -> EConstr.t -> unit Proofview.tactic

(** [wnia id ff] takes a formula [ff : BFormula (Formula Z) isProp]
    generates a witness and poses it as [id : seq ZMicromega.ZArithProof] *)
val wnia : Names.Id.t -> EConstr.t -> unit Proofview.tactic

(** [wsos_Q id ff] takes a formula [ff : BFormula (Formula Q) isProp]
    generates a witness and poses it as [id : seq (Psatz Q)] *)
val wsos_Q : Names.Id.t -> EConstr.t -> unit Proofview.tactic

(** [wsos_Z id ff] takes a formula [ff : BFormula (Formula Z) isProp]
    generates a witness and poses it as [id : seq ZMicromega.ZArithProof] *)
val wsos_Z : Names.Id.t -> EConstr.t -> unit Proofview.tactic

(** [wpsatz_Q n id ff] takes a formula [ff : BFormula (Formula Q) isProp]
    generates a witness and poses it as [id : seq (Psatz Q)] *)
val wpsatz_Q : int -> Names.Id.t -> EConstr.t -> unit Proofview.tactic

(** [wpsatz_Z n id ff] takes a formula [ff : BFormula (Formula Z) isProp]
    generates a witness and poses it as [id : seq ZMicromega.ZArithProof] *)
val wpsatz_Z : int -> Names.Id.t -> EConstr.t -> unit Proofview.tactic

(** {5 Use Micromega independently from tactics. } *)

(** [dump_proof_term] generates the Coq representation of a Micromega proof witness *)
val dump_proof_term : Micromega.zArithProof -> EConstr.t
