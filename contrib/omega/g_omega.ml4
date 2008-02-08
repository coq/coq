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
(* Pierre Crégut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Coq_omega

(* arnaud: trucs factices *)
let tclTHEN = Tacticals.tclTHEN
let tclREPEAT = Tacticals.tclREPEAT
let tclPROGRESS = Tacticals.tclPROGRESS
let tclTHENLIST = Tacticals.tclTHENLIST

module Refiner =
  struct
    let abstract_extended_tactic = Tacticals.abstract_extended_tactic

  end

module Tacmach =
  struct
    type 'a sigma = 'a Tacticals.sigma
  end

(* arnaud: /trucs factices *)

let omega_tactic l = 
  let tacs = List.map 
    (function  
       | "nat" -> Tacinterp.interp <:tactic<zify_nat>>
       | "positive" -> Tacinterp.interp <:tactic<zify_positive>>
       | "N" -> Tacinterp.interp <:tactic<zify_N>>
       | "Z" -> Tacinterp.interp <:tactic<zify_op>>
       | s -> Util.error ("No Omega knowledge base for type "^s))
    (Util.list_uniquize (List.sort compare l))
  in 
  tclTHEN
    (tclREPEAT (tclPROGRESS (tclTHENLIST tacs)))
    omega_solver


TACTIC EXTEND omega
|  [ "omega" ] -> [ Util.anomaly "G_omega.omega: à restaurer" (* arnaud: omega_tactic [] *) ]
END

TACTIC EXTEND omega'
| [ "omega" "with" ne_ident_list(l) ] -> 
    [ Util.anomaly "G_omega.omega': à restaurer" (* arnaud: omega_tactic (List.map Names.string_of_id l)*) ]
| [ "omega" "with" "*" ] -> [ Util.anomaly "G_omega.omega': à restaurer" (* arnaud: omega_tactic ["nat";"positive";"N";"Z"] *)]
END

