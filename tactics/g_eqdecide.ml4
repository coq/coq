(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*                              EqDecide                               *)
(*   A tactic for deciding propositional equality on inductive types   *)
(*                           by Eduardo Gimenez                        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Eqdecide

DECLARE PLUGIN "g_eqdecide"

TACTIC EXTEND decide_equality
| [ "decide" "equality" ] -> [ decideEqualityGoal ]
END

TACTIC EXTEND compare
| [ "compare" constr(c1) constr(c2) ] -> [ compare c1 c2 ]
END
