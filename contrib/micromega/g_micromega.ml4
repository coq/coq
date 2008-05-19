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

(* $Id:$ *)

open Quote
open Ring
open Mutils
open Rawterm
open Util

let out_arg = function
  | ArgVar _ -> anomaly "Unevaluated or_var variable"
  | ArgArg x -> x

TACTIC EXTEND Micromega
| [ "micromegap" int_or_var(i) ] -> [ Coq_micromega.micromega (out_arg i) ]
| [ "micromegap" ] -> [ Coq_micromega.micromega (-1) ]
END

TACTIC EXTEND Sos
[ "sosp" ] -> [ Coq_micromega.sos]
END


TACTIC EXTEND Omicron
[ "omicronp"  ] -> [ Coq_micromega.omicron]
END

TACTIC EXTEND QOmicron
[ "qomicronp"  ] -> [ Coq_micromega.qomicron]
END


TACTIC EXTEND ZOmicron
[ "zomicronp"  ] -> [ Coq_micromega.zomicron]
END

TACTIC EXTEND ROmicron
[ "romicronp"  ] -> [ Coq_micromega.romicron]
END

TACTIC EXTEND RMicromega
| [ "rmicromegap" int_or_var(i) ] -> [ Coq_micromega.rmicromega (out_arg i) ]
| [ "rmicromegap" ] -> [ Coq_micromega.rmicromega (-1) ]
END
