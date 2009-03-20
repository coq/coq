(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008			        *)
(*                                                                      *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Quote
open Ring
open Mutils
open Rawterm
open Util

let out_arg = function
  | ArgVar _ -> anomaly "Unevaluated or_var variable"
  | ArgArg x -> x

TACTIC EXTEND PsatzZ
| [ "psatz_Z" int_or_var(i) ] -> [ Coq_micromega.psatz_Z (out_arg i) ]
| [ "psatz_Z" ] -> [ Coq_micromega.psatz_Z (-1) ]
END

TACTIC EXTEND Sos_Z
| [ "sos_Z" ] -> [ Coq_micromega.sos_Z]
   END

TACTIC EXTEND Sos_Q
| [ "sos_Q" ] -> [ Coq_micromega.sos_Q]
   END

TACTIC EXTEND Sos_R
| [ "sos_R" ] -> [ Coq_micromega.sos_R]
END


TACTIC EXTEND Omicron
[ "psatzl_Z"  ] -> [ Coq_micromega.psatzl_Z]
END

TACTIC EXTEND QOmicron
[ "psatzl_Q"  ] -> [ Coq_micromega.psatzl_Q]
END


TACTIC EXTEND ZOmicron
[ "xlia"  ] -> [ Coq_micromega.xlia]
END

TACTIC EXTEND ROmicron
[ "psatzl_R"  ] -> [ Coq_micromega.psatzl_R]
END

TACTIC EXTEND RMicromega
| [ "psatz_R" int_or_var(i) ] -> [ Coq_micromega.psatz_R (out_arg i) ]
| [ "psatz_R" ] -> [ Coq_micromega.psatz_R (-1) ]
END


TACTIC EXTEND QMicromega
| [ "psatz_Q" int_or_var(i) ] -> [ Coq_micromega.psatz_Q (out_arg i) ]
| [ "psatz_Q" ] -> [ Coq_micromega.psatz_Q (-1) ]
END

