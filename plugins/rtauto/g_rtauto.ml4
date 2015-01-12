(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma"  i*)

DECLARE PLUGIN "rtauto_plugin"

TACTIC EXTEND rtauto
  [ "rtauto" ] -> [ Proofview.V82.tactic (Refl_tauto.rtauto_tac) ]
END

