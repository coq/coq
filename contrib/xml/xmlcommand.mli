(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project      *)
(*         *   University of Bologna                                   *)
(***********************************************************************)

(* Copyright (C) 2000-2004, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.unibo.it/.
 *)

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
