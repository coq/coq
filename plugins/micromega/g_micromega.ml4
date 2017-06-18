(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(* * Mappings from Coq tactics to Caml function calls                   *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008			        *)
(*                                                                      *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Ltac_plugin
open Stdarg
open Tacarg

DECLARE PLUGIN "micromega_plugin"

TACTIC EXTEND RED
| [ "myred"  ] -> [ Tactics.red_in_concl ]
END



TACTIC EXTEND PsatzZ
| [ "psatz_Z" int_or_var(i) tactic(t) ] -> [  (Coq_micromega.psatz_Z i
                                               (Tacinterp.tactic_of_value ist t))
                                               ]
| [ "psatz_Z" tactic(t)] -> [  (Coq_micromega.psatz_Z (-1)) (Tacinterp.tactic_of_value ist t) ]
END

TACTIC EXTEND Lia
[ "xlia" tactic(t) ] -> [   (Coq_micromega.xlia (Tacinterp.tactic_of_value ist t)) ]
END

TACTIC EXTEND Nia
[ "xnlia" tactic(t) ] -> [  (Coq_micromega.xnlia (Tacinterp.tactic_of_value ist t)) ]
END

TACTIC EXTEND NRA
[ "xnra" tactic(t) ] -> [  (Coq_micromega.nra (Tacinterp.tactic_of_value ist t))]
END

TACTIC EXTEND NQA
[ "xnqa" tactic(t) ] -> [  (Coq_micromega.nqa (Tacinterp.tactic_of_value ist t))]
END


  
TACTIC EXTEND Sos_Z
| [ "sos_Z" tactic(t) ] -> [ (Coq_micromega.sos_Z (Tacinterp.tactic_of_value ist t)) ]
   END

TACTIC EXTEND Sos_Q
| [ "sos_Q" tactic(t) ] -> [   (Coq_micromega.sos_Q (Tacinterp.tactic_of_value ist t)) ]
   END

TACTIC EXTEND Sos_R
| [ "sos_R" tactic(t) ] -> [   (Coq_micromega.sos_R (Tacinterp.tactic_of_value ist t)) ]
END

TACTIC EXTEND LRA_Q
[ "lra_Q"  tactic(t) ] -> [   (Coq_micromega.lra_Q (Tacinterp.tactic_of_value ist t)) ]
END

TACTIC EXTEND LRA_R
[ "lra_R" tactic(t) ] -> [   (Coq_micromega.lra_R (Tacinterp.tactic_of_value ist t)) ]
END

TACTIC EXTEND PsatzR
| [ "psatz_R" int_or_var(i) tactic(t) ] -> [   (Coq_micromega.psatz_R i (Tacinterp.tactic_of_value ist t)) ]
| [ "psatz_R" tactic(t) ] -> [   (Coq_micromega.psatz_R (-1) (Tacinterp.tactic_of_value ist t)) ]
END

TACTIC EXTEND PsatzQ
| [ "psatz_Q" int_or_var(i) tactic(t) ] -> [  (Coq_micromega.psatz_Q i (Tacinterp.tactic_of_value ist t)) ]
| [ "psatz_Q" tactic(t) ] -> [  (Coq_micromega.psatz_Q (-1) (Tacinterp.tactic_of_value ist t)) ]
END

