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

open Constrarg

DECLARE PLUGIN "micromega_plugin"

TACTIC EXTEND PsatzZ
| [ "psatz_Z" int_or_var(i) ] -> [  (Coq_micromega.psatz_Z i) ]
| [ "psatz_Z" ] -> [  (Coq_micromega.psatz_Z (-1)) ]
END

TACTIC EXTEND Lia
[ "xlia"  ] -> [   (Coq_micromega.xlia) ]
END

TACTIC EXTEND Nia
[ "xnlia"  ] -> [  (Coq_micromega.xnlia) ]
END

TACTIC EXTEND NRA
[ "xnra"  ] -> [  (Coq_micromega.nra)]
END

TACTIC EXTEND NQA
[ "xnqa"  ] -> [  (Coq_micromega.nqa)]
END


  
TACTIC EXTEND Sos_Z
| [ "sos_Z" ] -> [ (Coq_micromega.sos_Z) ]
   END

TACTIC EXTEND Sos_Q
| [ "sos_Q" ] -> [   (Coq_micromega.sos_Q) ]
   END

TACTIC EXTEND Sos_R
| [ "sos_R" ] -> [   (Coq_micromega.sos_R) ]
END

TACTIC EXTEND LRA_Q
[ "lra_Q"  ] -> [   (Coq_micromega.lra_Q) ]
END

TACTIC EXTEND LRA_R
[ "lra_R"  ] -> [   (Coq_micromega.lra_R) ]
END

TACTIC EXTEND PsatzR
| [ "psatz_R" int_or_var(i) ] -> [   (Coq_micromega.psatz_R i) ]
| [ "psatz_R" ] -> [   (Coq_micromega.psatz_R (-1)) ]
END

TACTIC EXTEND PsatzQ
| [ "psatz_Q" int_or_var(i) ] -> [  (Coq_micromega.psatz_Q i) ]
| [ "psatz_Q" ] -> [  (Coq_micromega.psatz_Q (-1)) ]
END

