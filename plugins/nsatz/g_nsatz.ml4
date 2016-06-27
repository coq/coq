DECLARE PLUGIN "nsatz_plugin"

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "nsatz_plugin"

TACTIC EXTEND nsatz_compute
| [ "nsatz_compute"  constr(lt) ] -> [ Nsatz.nsatz_compute lt ]
END
