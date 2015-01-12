(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

open Coq_omega

let omega_tactic l =
  let tacs = List.map
    (function
       | "nat" -> Tacinterp.interp <:tactic<zify_nat>>
       | "positive" -> Tacinterp.interp <:tactic<zify_positive>>
       | "N" -> Tacinterp.interp <:tactic<zify_N>>
       | "Z" -> Tacinterp.interp <:tactic<zify_op>>
       | s -> Errors.error ("No Omega knowledge base for type "^s))
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

