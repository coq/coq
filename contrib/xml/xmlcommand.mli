(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                     A module to print Coq objects in XML                   *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 07/12/2000                                 *)
(*                                                                            *)
(* This module defines a pretty-printer and the stream of commands to the pp  *)
(*                                                                            *)
(******************************************************************************)

(*i $Id$ i*)

(* print id dest                                                          *)
(*  where id   is the identifier (name) of a definition/theorem or of an  *)
(*             inductive definition                                       *)
(*  and   dest is either None (for stdout) or (Some filename)             *)
(* pretty prints via Xml.pp the object whose identifier is id on dest     *)
(* Note: it is printed only (and directly) the most discharged available  *)
(*       form of the definition (all the parameters are                   *)
(*       lambda-abstracted, but the object can still refer to variables)  *)
val print : bool -> Libnames.global_reference -> string option -> unit

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
