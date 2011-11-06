(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
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

(*i $Id$ i*)

(* print_global qid fn                                                    *)
(*  where qid  is a long name denoting a definition/theorem or            *)
(*             an inductive definition                                    *)
(*  and   dest is either None (for stdout) or (Some filename)             *)
(* pretty prints via Xml.pp the object whose name is ref on dest          *)
(* Note: it is printed only (and directly) the most discharged available  *)
(*       form of the definition (all the parameters are                   *)
(*       lambda-abstracted, but the object can still refer to variables)  *)
val print_ref : Libnames.reference -> string option -> unit

(* show dest                                                  *)
(*  where dest is either None (for stdout) or (Some filename) *)
(* pretty prints via Xml.pp the proof in progress on dest     *)
val show : string option -> unit

(* set_print_proof_tree f                                      *)
(*  sets a callback function f to export the proof_tree to XML *)
val set_print_proof_tree :
    (string ->
     Evd.evar_map ->
     Proof_type.proof_tree ->
     Term.constr Proof2aproof.ProofTreeHash.t ->
     Proof_type.proof_tree Proof2aproof.ProofTreeHash.t ->
     string Acic.CicHash.t -> Xml.token Stream.t) ->
    unit
