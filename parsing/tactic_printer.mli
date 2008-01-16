(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Sign
open Evd
open Tacexpr
(*i*)
(* arnaud: trucs factices *)
type proof_tree
type rule
(* arnaud: /trucs factices *)

(* These are the entry points for tactics, proof trees, ... *)

val print_proof : evar_map -> named_context -> proof_tree -> std_ppcmds
val pr_rule     : rule -> std_ppcmds
val pr_tactic   : Pptactic.Proof_type.tactic_expr -> std_ppcmds
val print_script :
  bool -> evar_map -> proof_tree -> std_ppcmds
val print_treescript :
  bool -> evar_map -> proof_tree -> std_ppcmds
