(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names

module type Pp =
sig
  val pr_mutual_inductive_body : Environ.env -> mutual_inductive -> Declarations.mutual_inductive_body -> std_ppcmds
  val print_module : bool -> module_path -> std_ppcmds
  val print_modtype : module_path -> std_ppcmds
end
