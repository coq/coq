(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* Correctness is base on the tactic Refine (developped on purpose) *)

Require Export Refine.

Require Export Tuples.

Require Export ProgInt.
Require Export ProgBool.
Require Export ProgWf.

Require Export Arrays.

Declare ML Module
    "misc_utils" "effects" "renamings" "progTypes" "progAst"
    "prog_errors" "prog_env" "prog_utils"
    "prog_db" "prog_cci" "monad" "tradEnv"
    "prog_red" "prog_typing" "prog_wp" "mlise" "prog_tactic"
    "pprog".

Token "'".




