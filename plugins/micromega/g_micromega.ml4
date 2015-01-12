(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

open Errors
open Misctypes

DECLARE PLUGIN "micromega_plugin"

let out_arg = function
  | ArgVar _ -> anomaly (Pp.str "Unevaluated or_var variable")
  | ArgArg x -> x

TACTIC EXTEND PsatzZ
| [ "psatz_Z" int_or_var(i) ] -> [ Proofview.V82.tactic (Coq_micromega.psatz_Z (out_arg i)) ]
| [ "psatz_Z" ] -> [ Proofview.V82.tactic (Coq_micromega.psatz_Z (-1)) ]
END

TACTIC EXTEND Lia
[ "xlia"  ] -> [  Proofview.V82.tactic (Coq_micromega.xlia) ]
END

TACTIC EXTEND Nia
[ "xnlia"  ] -> [  Proofview.V82.tactic (Coq_micromega.xnlia) ]
END



TACTIC EXTEND Sos_Z
| [ "sos_Z" ] -> [  Proofview.V82.tactic (Coq_micromega.sos_Z) ]
   END

TACTIC EXTEND Sos_Q
| [ "sos_Q" ] -> [  Proofview.V82.tactic (Coq_micromega.sos_Q) ]
   END

TACTIC EXTEND Sos_R
| [ "sos_R" ] -> [  Proofview.V82.tactic (Coq_micromega.sos_R) ]
END

(*
TACTIC EXTEND Omicron
[ "psatzl_Z"  ] -> [  Proofview.V82.tactic (Coq_micromega.psatzl_Z) ]
END
*)

TACTIC EXTEND LRA_Q
[ "psatzl_Q"  ] -> [  Proofview.V82.tactic (Coq_micromega.psatzl_Q) ]
END

TACTIC EXTEND LRA_R
[ "psatzl_R"  ] -> [  Proofview.V82.tactic (Coq_micromega.psatzl_R) ]
END

TACTIC EXTEND PsatzR
| [ "psatz_R" int_or_var(i) ] -> [  Proofview.V82.tactic (Coq_micromega.psatz_R (out_arg i)) ]
| [ "psatz_R" ] -> [  Proofview.V82.tactic (Coq_micromega.psatz_R (-1)) ]
END

TACTIC EXTEND PsatzQ
| [ "psatz_Q" int_or_var(i) ] -> [ Proofview.V82.tactic (Coq_micromega.psatz_Q (out_arg i)) ]
| [ "psatz_Q" ] -> [ Proofview.V82.tactic (Coq_micromega.psatz_Q (-1)) ]
END

