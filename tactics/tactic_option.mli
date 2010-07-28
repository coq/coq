(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: subtac.ml 12623 2010-01-04 17:50:38Z letouzey $ *)

open Proof_type
open Tacexpr
open Vernacexpr

val declare_tactic_option : ?default:Tacexpr.glob_tactic_expr -> string -> 
  (* put *) (locality_flag -> glob_tactic_expr -> unit) *
  (* get *) (unit -> locality_flag * tactic) *
  (* print *) (unit -> Pp.std_ppcmds)
