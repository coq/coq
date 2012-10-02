(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Sign
open Evd
open Proof_type

(** These are the entry points for tactics, proof trees, ... *)

val print_proof : evar_map -> named_context -> proof_tree -> Pp.std_ppcmds
val pr_rule     : rule -> Pp.std_ppcmds
val pr_tactic   : tactic_expr -> Pp.std_ppcmds
val print_script :
  ?nochange:bool -> evar_map -> proof_tree -> Pp.std_ppcmds
val print_treescript :
  ?nochange:bool -> evar_map -> proof_tree -> Pp.std_ppcmds
