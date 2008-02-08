(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Dp

(* arnaud: trucs factices *)
module Refiner =
  struct
    let abstract_extended_tactic = Tacticals.abstract_extended_tactic
  end
(* arnaud: /trucs factices *)

TACTIC EXTEND Simplify
  [ "simplify" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: simplify  *) ]
END

TACTIC EXTEND Ergo
  [ "ergo" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: ergo *) ]
END

TACTIC EXTEND Yices
  [ "yices" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: yices *) ]
END

TACTIC EXTEND CVCLite
  [ "cvcl" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: cvc_lite *) ]
END

TACTIC EXTEND Harvey
  [ "harvey" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: harvey *) ]
END

TACTIC EXTEND Zenon
  [ "zenon" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: zenon *) ]
END

TACTIC EXTEND Gwhy
  [ "gwhy" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: gwhy *) ]
END

(* should be part of basic tactics syntax *)
TACTIC EXTEND admit
  [ "admit"    ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: Tactics.admit_as_an_axiom *) ]
END

VERNAC COMMAND EXTEND Dp_hint 
  [ "Dp_hint" ne_global_list(l) ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: dp_hint l *) ]
END

VERNAC COMMAND EXTEND Dp_timeout
| [ "Dp_timeout" natural(n) ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: set_timeout n *) ]
END

VERNAC COMMAND EXTEND Dp_debug
| [ "Dp_debug" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: set_debug true; Dp_zenon.set_debug true *) ]
END

VERNAC COMMAND EXTEND Dp_trace
| [ "Dp_trace" ] -> [ Util.anomaly "Dp.[...]: à restaurer" (* arnaud: set_trace true *) ]
END

