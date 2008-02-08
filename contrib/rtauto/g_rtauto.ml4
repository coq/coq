(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$*)

(*i camlp4deps: "parsing/grammar.cma"  i*)

(* arnaud: trucs factices *)
module Refiner =
  struct
    let abstract_extended_tactic = Tacticals.abstract_extended_tactic
  end
(* arnaud: /trucs factices *)

TACTIC EXTEND rtauto
  [ "rtauto" ] -> [ Util.anomaly "G_rtauto.rtauto: à restaurer" (* arnaud: Refl_tauto.rtauto_tac *) ]
END

