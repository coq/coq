(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tacintern
open Decl_expr


val intern_proof_instr : glob_sign -> raw_proof_instr -> glob_proof_instr
val interp_proof_instr : Decl_mode.pm_info ->
  Environ.env -> Evd.evar_map -> glob_proof_instr -> proof_instr
