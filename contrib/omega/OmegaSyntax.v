(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(**************************************************************************)
(*                                                                        *)
(* Omega: a solver of quantifier-free problems in Presburger Arithmetic   *)
(*                                                                        *)
(* Pierre Crégut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(* $Id$ *)

Grammar vernac vernac : ast :=
  omega_sett [ "Set" "Omega" "Time" "." ] -> [(OmegaFlag "+time")]
| omega_sets [ "Set" "Omega" "System" "." ] -> [(OmegaFlag "+system")]
| omega_seta [ "Set" "Omega" "Action" "." ] -> [(OmegaFlag "+action")]
| omega_unst [ "Unset" "Omega" "Time" "." ] -> [(OmegaFlag "-time")]
| omega_unss [ "Unset" "Omega" "System" "." ] -> [(OmegaFlag "-system")]
| omega_unsa [ "Unset" "Omega" "Action" "." ] -> [(OmegaFlag "-action")]
| omega_swit [ "Switch" "Omega" "Time" "." ] -> [(OmegaFlag "time")]
| omega_swis [ "Switch" "Omega" "System" "." ] -> [(OmegaFlag "system")]
| omega_swia [ "Switch" "Omega" "Action" "." ] -> [(OmegaFlag "action")]
| omega_set  [ "Set" "Omega" stringarg($id) "." ] -> [(OmegaFlag $id)].


Grammar tactic simple_tactic : ast :=
  omega [ "Omega" ] -> [(Omega)].

Syntax tactic level 0:
  omega [ << (Omega) >> ] -> ["Omega"].
