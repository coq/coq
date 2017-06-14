(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(**************************************************************************)
(*                                                                        *)
(* Omega: a solver of quantifier-free problems in Presburger Arithmetic   *)
(*                                                                        *)
(* Pierre Crégut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)


DECLARE PLUGIN "omega_plugin"

open Ltac_plugin
open Names
open Coq_omega
open Stdarg

let eval_tactic name =
  let dp = DirPath.make (List.map Id.of_string ["PreOmega"; "omega"; "Coq"]) in
  let kn = KerName.make2 (ModPath.MPfile dp) (Label.make name) in
  let tac = Tacenv.interp_ltac kn in
  Tacinterp.eval_tactic tac

let omega_tactic l =
  let tacs = List.map
    (function
       | "nat" -> eval_tactic "zify_nat"
       | "positive" -> eval_tactic "zify_positive"
       | "N" -> eval_tactic "zify_N"
       | "Z" -> eval_tactic "zify_op"
       | s -> CErrors.user_err Pp.(str ("No Omega knowledge base for type "^s)))
    (Util.List.sort_uniquize String.compare l)
  in
  Tacticals.New.tclTHEN
    (Tacticals.New.tclREPEAT (Tacticals.New.tclTHENLIST tacs))
    (omega_solver)


TACTIC EXTEND omega
|  [ "omega" ] -> [ omega_tactic [] ]
END

TACTIC EXTEND omega'
| [ "omega" "with" ne_ident_list(l) ] ->
    [ omega_tactic (List.map Names.Id.to_string l) ]
| [ "omega" "with" "*" ] -> [ omega_tactic ["nat";"positive";"N";"Z"] ]
END

