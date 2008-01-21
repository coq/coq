(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(**************************************************************************)
(*                                                                        *)
(* Omega: a solver of quantifier-free problems in Presburger Arithmetic   *)
(*                                                                        *)
(* Pierre Cr�gut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

(* arnaud: trucs factices *)
module Refiner =
  struct
    let abstract_extended_tactic = Tacticals.abstract_extended_tactic
  end
module Tacmach =
  struct
    let project _ = Util.anomaly "G_eterm.project: fantome"
    let pf_concl _ = Util.anomaly "G_eterm.pf_concl: fantome"
  end
(* arnaud: /trucs factices *)

open Eterm

TACTIC EXTEND eterm
  [ "eterm" ] -> [ 
    (fun gl ->
       let evm = Tacmach.project gl and t = Tacmach.pf_concl gl in
         Eterm.etermtac (evm, t) gl) ]
END
