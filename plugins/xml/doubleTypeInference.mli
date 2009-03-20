(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

type types = { synthesized : Term.types; expected : Term.types option; } 

val cprop : Names.constant

val whd_betadeltaiotacprop :
  Environ.env -> Evd.evar_map -> Term.constr -> Term.constr

val double_type_of :
  Environ.env -> Evd.evar_map -> Term.constr -> Term.constr option ->
   types Acic.CicHash.t -> unit
